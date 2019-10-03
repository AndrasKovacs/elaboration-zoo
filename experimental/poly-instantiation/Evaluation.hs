{-# options_ghc -Wno-type-defaults #-}

module Evaluation where

import Lens.Micro.Platform
import qualified Data.IntMap.Strict as M

import Types
import Debug.Trace


-- | Force head constructor + spine.
force :: MCxt -> Val -> Val
force ms v = trace "force" $  case v of
  VNe h sp ->
    let go h SNil             = h
        go h (SApp sp u i)    = vApp (go h sp) u i
        go h (SAppTel a sp u) = vAppTel ms a (go h sp) u
        go h (SProj1 sp)      = vProj1 (go h sp)
        go h (SProj2 sp)      = vProj2 (go h sp)
    in case h of
      HMeta m | Solved v <- ms M.! m -> force ms $ go v sp
      HMeta m -> go (VMeta m) sp
      HVar x  -> go (VVar x) sp
  v -> v

forceM :: Val -> M cxt Val
forceM v = force <$> use mcxt <*> pure v

-- -- | Forcing a spine computes all telescope applications.
-- forceSp :: MCxt -> Spine -> Spine
-- forceSp ms sp = go sp where
--   go :: Spine -> Spine
--   go SNil             = SNil
--   go (SApp sp u i)    = SApp (go sp) u i
--   go (SAppTel a sp u) = loop a (go sp) u where
--     loop a t ~u = case force ms a of
--       VTCons x a b ->
--         let ~u1 = vProj1 u
--         in loop (b u1) (SApp t u1 Impl) (vProj2 u)
--       VTEmpty      -> t
--       a            -> SAppTel a t u
--   go (SProj1 sp)      = SProj1 (go sp)
--   go (SProj2 sp)      = SProj2 (go sp)

-- forceSpM :: Spine -> M cxt Spine
-- forceSpM sp = forceSp <$> use mcxt <*> pure sp

vApp :: Val -> Val -> Icit -> Val
vApp (VLam _ _ t) ~u i = t u
vApp (VNe h sp)   ~u i = VNe h (SApp sp u i)
vApp (VLamTel{})  _  _ = error "lamtel"
vApp _            _  i = error "impossible"

vProj1 :: Val -> Val
vProj1 (VTcons t u) = t
vProj1 (VNe h sp)   = VNe h (SProj1 sp)
vProj1 _            = error "impossible"

vProj2 :: Val -> Val
vProj2 (VTcons t u) = u
vProj2 (VNe h sp)   = VNe h (SProj2 sp)
vProj2 _            = error "impossible"

vPiTel :: MCxt -> Name -> VTy -> (Val -> Val) -> Val
vPiTel ms x a b = case force ms a of
  VTEmpty -> b VTempty
  VTCons x1 a as ->
    VPi x1 Impl a $ \ ~x1 -> vPiTel ms (x ++ "2") (as x1) $ \ ~x2 -> b (VTcons x1 x2)
  a -> VPiTel x a b

vAppTel :: MCxt -> VTy -> Val -> Val -> Val
vAppTel ms a t ~u = case force ms a of
  VTEmpty       -> t
  VTCons _ a as -> let v1 = vProj1 u in vAppTel ms (as v1) (vApp t v1 Impl) (vProj2 u)
  a             -> case t of
    VLamTel _ _ t -> t u
    VNe h sp      -> VNe h (SAppTel a sp u)
    _             -> error "impossible"

vLamTel :: MCxt -> Name -> VTy -> (Val -> Val) -> Val
vLamTel ms x a t = case force ms a of
  VTEmpty -> t VTempty
  VTCons x1 a as ->
    VLam x1 Impl $ \ ~x1 -> vLamTel ms (x ++ "2") (as x1) $ \ ~x2 -> t (VTcons x1 x2)
  a -> VLamTel x a t

eval :: MCxt -> Vals -> Tm -> Val
eval ms = go where
  goBind vs x t = \ ~u -> go ((x, Just u):vs) t
  go vs = \case
    Var x        -> case lookup x vs of
                      Nothing -> error $ show (x, map fst vs)
                      Just mv -> maybe (VVar x) id mv
    Let x _ t u  -> goBind vs x u (go vs t)
    U            -> VU
    Meta m       -> case ms M.! m of Solved v -> v; _ -> VMeta m
    Pi x i a b   -> VPi x i (go vs a) (goBind vs x b)
    Lam x i t    -> VLam x i (goBind vs x t)
    App t u i    -> traceShow [(x, case e of Solved{} -> True; _ -> False) | (x, e) <- M.assocs  ms] $
                    (traceShow ("app", nf ms vs t, nf ms vs u, i) $
                    vApp (go vs t) (go vs u) i)

    Tel          -> VTel
    Rec a        -> VRec (go vs a)
    TEmpty       -> VTEmpty
    TCons x a b  -> VTCons x (go vs a) (goBind vs x b)
    Tempty       -> VTempty
    Tcons t u    -> VTcons (go vs t) (go vs u)
    Proj1 t      -> vProj1 (go vs t)
    Proj2 t      -> vProj2 (go vs t)

    PiTel x a b  -> vPiTel  ms x (go vs a) (goBind vs x b)
    AppTel a t u -> vAppTel ms (go vs a) (go vs t) (go vs u)
    LamTel x a t -> vLamTel ms x (go vs a) (goBind vs x t)

evalM :: HasVals cxt Vals => Tm -> M cxt Val
evalM t = eval <$> use mcxt <*> view vals <*> pure t

fresh :: Vals -> Name -> Name
fresh vs "_" = "_"
fresh vs x = case lookup x vs of
  Just _  -> fresh vs (x ++ "'")
  Nothing -> x

freshM :: HasVals cxt Vals => Name -> M cxt Name
freshM x = fresh <$> view vals <*> pure x

-- |  Quote into fully forced normal forms.
quote :: MCxt -> Vals -> Val -> Tm
quote ms = go where

  goBind vs x t = go ((x, Nothing):vs) (t (VVar x))

  go vs v = case force ms v of
    VNe h sp ->
      let goSp :: Spine -> Tm
          goSp SNil = case h of
            HMeta x    -> Meta x
            HVar x     -> Var x
          goSp (SApp sp u i)    = App (goSp sp) (go vs u) i
          goSp (SAppTel a sp u) = AppTel (go vs a) (goSp sp) (go vs u)
          goSp (SProj1 sp)      = Proj1 (goSp sp)
          goSp (SProj2 sp)      = Proj2 (goSp sp)
      in goSp sp -- (forceSp ms sp)

    VLam (fresh vs -> x) i t    -> Lam x i (goBind vs x t)
    VPi  (fresh vs -> x) i a b  -> Pi x i (go vs a) (goBind vs x b)
    VU                          -> U
    VTel                        -> Tel
    VRec a                      -> Rec (go vs a)
    VTEmpty                     -> TEmpty
    VTCons (fresh vs -> x) a as -> TCons x (go vs a) (goBind vs x as)
    VTempty                     -> Tempty
    VTcons t u                  -> Tcons (go vs t) (go vs u)
    VPiTel (fresh vs -> x) a b  -> PiTel x (go vs a) (goBind vs x b)
    VLamTel (fresh vs -> x) a t -> LamTel x (go vs a) (goBind vs x t)

quoteM :: HasVals cxt Vals => Val -> M cxt Tm
quoteM v = quote <$> use mcxt <*> view vals <*> pure v

nf :: MCxt -> Vals -> Tm -> Tm
nf ms vs = quote ms vs . eval ms vs

nfM :: HasVals cxt Vals => Tm -> M cxt Tm
nfM t = quoteM =<< evalM t
