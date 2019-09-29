
module Evaluation where

import Data.Maybe
import Lens.Micro.Platform
import qualified Data.IntMap.Strict as M

import Presyntax
import Types

-- | Forcing: forces not only the head symbol, but also the
--   shape of the spine, via forcing the telescope apps.
force :: MCxt -> Val -> Val
force ms = \case
  VNe (HMeta m) sp | Solved t <- ms M.! m ->
    let go SNil             = t
        go (SApp sp u i)    = vApp (go sp) u i
        go (SAppTel a sp u) = vAppTel (force ms a) (go sp) u
        go (SProj1 sp)      = vProj1 (go sp)
        go (SProj2 sp)      = vProj2 (go sp)
    in force ms (go sp)
  v -> v

forceM :: Val -> M cxt Val
forceM v = force <$> use mcxt <*> pure v

vApp :: Val -> Val -> Icit -> Val
vApp (VLam _ _ t) ~u i = t u
vApp (VNe h sp)   ~u i = VNe h (SApp sp u i)
vApp _            _  i = error "impossible"

vProj1 :: Val -> Val
vProj1 (VTcons t u) = t
vProj1 (VNe h sp)   = VNe h (SProj1 sp)
vProj1 _            = error "impossible"

vProj2 :: Val -> Val
vProj2 (VTcons t u) = u
vProj2 (VNe h sp)   = VNe h (SProj2 sp)
vProj2 _            = error "impossible"

vPiTel :: Name -> VTy -> (Val -> Val) -> Val
vPiTel x VTEmpty       b = b VTempty
vPiTel x (VTCons a as) b =
  VPi (x ++ "1") Impl a $ \ ~x1 -> vPiTel (x ++ "2") as $ \ ~x2 -> b (VTcons x1 x2)
vPiTel x a b = VPiTel x a b

vAppTel :: VTy -> Val -> Val -> Val
vAppTel VTEmpty       t ~u = t
vAppTel (VTCons a as) t ~u = vAppTel as (vApp t (vProj1 u) Impl)
                                        (vProj2 u)
vAppTel a (VLamTel _ _ t) ~u = t u
vAppTel a (VNe h sp)      ~u = VNe h (SAppTel a sp u)
vAppTel _ _                _ = error "impossible"

vLamTel :: Name -> VTy -> (Val -> Val) -> Val
vLamTel x VTEmpty       t = t VTempty
vLamTel x (VTCons a as) t =
  VLam (x ++ "1") Impl $ \ ~x1 -> vLamTel (x ++ "2") as $ \ ~x2 -> t (VTcons x1 x2)
vLamTel x a t = VLamTel x a t

eval :: MCxt -> Vals -> Tm -> Val
eval ms = go where
  goBind vs x t = \u -> go ((x, Right u):vs) t
  go vs = \case
    Var x        -> either (\_ -> VVar x) id (fromJust $ lookup x vs)
    Let x _ t u  -> go ((x, Right (go vs t)):vs) u
    U            -> VU
    Meta m       -> case ms M.! m of Solved t -> t; _ -> VMeta m
    Pi x i a b   -> VPi x i (go vs a) (goBind vs x b)
    Lam x i t    -> VLam x i (goBind vs x t)
    App t u i    -> vApp (go vs t) (go vs u) i

    Tel          -> VTel
    El a         -> VEl (go vs a)
    TEmpty       -> VTEmpty
    TCons a b    -> VTCons (go vs a) (go vs b)
    Tempty       -> VTempty
    Tcons t u    -> VTcons (go vs t) (go vs u)
    Proj1 t      -> vProj1 (go vs t)
    Proj2 t      -> vProj2 (go vs t)

    PiTel x a b  -> vPiTel x (go vs a) (goBind vs x b)
    AppTel a t u -> vAppTel (go vs a) (go vs t) (go vs u)
    LamTel x a t -> vLamTel x (go vs a) (goBind vs x t)

evalM :: HasVals cxt Vals => Tm -> M cxt Val
evalM t = eval <$> use mcxt <*> view vals <*> pure t

fresh :: Vals -> Name -> Name
fresh vs "_" = "_"
fresh vs x = case lookup x vs of
  Just _  -> fresh vs (x ++ "'")
  Nothing -> x

-- |  Quote into fully forced normal forms.
quote :: MCxt -> Vals -> Val -> Tm
quote ms = go where
  goBind vs x t = go ((x, Left Nothing):vs) (t (VVar x))
  goTelBind vs x a t = go ((x, Left (Just a)):vs) (t (VVar x))
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
      in goSp sp

    VLam (fresh vs -> x) i t    -> Lam x i (goBind vs x t)
    VPi  (fresh vs -> x) i a b  -> Pi x i (go vs a) (goBind vs x b)
    VU                          -> U
    VTel                        -> Tel
    VEl a                       -> El (go vs a)
    VTEmpty                     -> TEmpty
    VTCons a as                 -> TCons (go vs a) (go vs as)
    VTempty                     -> Tempty
    VTcons t u                  -> Tcons (go vs t) (go vs u)
    VPiTel (fresh vs -> x) a b  -> PiTel x (go vs a) (goTelBind vs x a b)
    VLamTel (fresh vs -> x) a t -> LamTel x (go vs a) (goTelBind vs x a t)

quoteM :: HasVals cxt Vals => Val -> M cxt Tm
quoteM v = quote <$> use mcxt <*> view vals <*> pure v

nfM :: HasVals cxt Vals => Tm -> M cxt Tm
nfM t = quoteM =<< evalM t
