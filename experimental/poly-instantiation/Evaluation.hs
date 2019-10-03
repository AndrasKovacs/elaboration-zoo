{-# options_ghc -Wno-type-defaults -Wno-unused-imports #-}

module Evaluation where

import Control.Monad
import Control.Monad.Reader
import Lens.Micro.Platform

import qualified Data.IntMap.Strict as M

import Types
import Debug.Trace

runEval :: EvalM a -> MCxt -> Vals -> a
runEval ma ms vs = runReader ma (EvalEnv ms vs)

vProj1 :: Val -> Val
vProj1 (VTcons t u) = t
vProj1 (VNe h sp)   = VNe h (SProj1 sp)
vProj1 _            = error "impossible"

vProj2 :: Val -> Val
vProj2 (VTcons t u) = u
vProj2 (VNe h sp)   = VNe h (SProj2 sp)
vProj2 _            = error "impossible"

vVar :: Name -> EvalM Val
vVar x = do
  vs <- view vals
  case lookup x vs of
    Nothing -> error "impossible"
    Just mv -> pure $ maybe (VVar x) id mv

lookupMeta :: MId -> EvalM MetaEntry
lookupMeta m = do
  ms <- view mcxt
  case M.lookup m ms of
    Just e  -> pure e
    Nothing -> error "impossible"

vMeta :: MId -> EvalM Val
vMeta m = lookupMeta m >>= \case
  Solved v -> pure v
  _        -> pure (VMeta m)

defining :: Name -> Val -> EvalM a -> EvalM a
defining x ~v ma = local (vals %~ ((x, Just v):)) ma

hlam :: (Val -> EvalM Val) -> EvalM Closure
hlam t = do
  vs <- view vals
  pure $ \ms ~v -> runEval (t v) ms vs

close :: Name -> Tm -> EvalM Closure
close x t = hlam (\ ~v -> defining x v $ eval t)

apply :: Closure -> Val -> EvalM Val
apply cl ~u = cl <$> view mcxt <*> pure u

-- | Force the outermost constructor in a value, if it's a neutral value
--   then also force the *shape* of the spine as well.
force :: Val -> EvalM Val
force = \case
  VNe h sp -> do
    let go :: Val -> Spine -> EvalM Val
        go ~h SNil             = pure h
        go ~h (SApp sp u i)    = do {sp <- go h sp; vApp sp u i}
        go ~h (SAppTel a sp u) = do {sp <- go h sp; vAppTel a sp u}
        go ~h (SProj1 sp)      = vProj1 <$> go h sp
        go ~h (SProj2 sp)      = vProj2 <$> go h sp

    case h of
      HVar x -> go (VVar x) sp
      HMeta m -> lookupMeta m >>= \case
        Unsolved{} -> go (VMeta m) sp
        Solved v   -> force =<< go v sp

  VPiTel x a b  -> vPiTel force x a b
  VLamTel x a t -> vLamTel force x a t
  v             -> pure v

-- We parameterize vPiTel and vLamTel with a continuation, because
-- sometimes we want to force the result, but sometimes don't.
vPiTel :: (Val -> EvalM Val) -> Name -> VTy -> Closure -> EvalM Val
vPiTel k x a b = force a >>= \case
  VTEmpty        -> k =<< apply b VTempty
  VTCons x1 a as ->
    VPi x1 Impl a <$> hlam (\ ~x1 ->
      join (vPiTel pure (x ++ "2") <$> apply as x1 <*> hlam (\ ~x2 ->
        apply b (VTcons x1 x2)
        )))
  a -> pure (VPiTel x a b)

vLamTel :: (Val -> EvalM Val) -> Name -> VTy -> Closure -> EvalM Val
vLamTel k x a t = force a >>= \case
  VTEmpty        -> k =<< apply t VTempty
  VTCons x1 a as ->
    VLam x1 Impl <$> hlam (\ ~x1 ->
      join (vLamTel k (x ++ "2") <$> apply as x1 <*> hlam (\ ~x2 ->
        apply t (VTcons x1 x2)
        )))
  a -> pure (VLamTel x a t)

vAppTel ::  VTy -> Val -> Val -> EvalM Val
vAppTel t a ~u =
  force a >>= \case
    VTEmpty       -> pure t
    VTCons _ a as ->
      let v1 = vProj1 u in
      join (vAppTel <$> apply as v1 <*> vApp t v1 Impl <*> pure (vProj2 u))
    a -> case t of
      VLamTel _ _ t -> apply t u
      VNe h sp      -> pure $ VNe h (SAppTel a sp u)
      _             -> error "impossible"

vApp :: Val -> Val -> Icit -> EvalM Val
vApp (VLam _ _ t   ) ~u i    = apply t u
vApp (VNe h sp     ) ~u i    = pure $ VNe h (SApp sp u i)
vApp (VLamTel x a t) ~u Impl = do {t <- vLamTel pure x a t; vApp t u Impl}
vApp _                _ _    = error "impossible"


eval :: Tm -> EvalM Val
eval = go where
  go :: Tm -> EvalM Val
  go = \case
    Var x        -> vVar x
    Let x _ t u  -> do {~v <- go t; defining x v $ go u}
    U            -> pure VU
    Meta m       -> vMeta m
    Pi x i a b   -> VPi x i <$> go a <*> close x b
    Lam x i t    -> VLam x i <$> close x t
    App t u i    -> join (vApp <$> go t <*> go u <*> pure i)
    Tel          -> pure VTel
    TEmpty       -> pure VTEmpty
    TCons x a b  -> VTCons x <$> go a <*> close x b
    Rec a        -> VRec <$> go a
    Tempty       -> pure VTempty
    Tcons t u    -> VTcons <$> go t <*> go u
    Proj1 t      -> vProj1 <$> go t
    Proj2 t      -> vProj2 <$> go t
    PiTel x a b  -> join (vPiTel pure x <$> go a <*> close x b)
    AppTel a t u -> join (vAppTel <$> go a <*> go t <*> go u)
    LamTel x a t -> join (vLamTel pure x <$> go a <*> close x t)

embedEvalM :: HasVals cxt Vals => EvalM a -> M cxt a
embedEvalM ma = runEval ma <$> use mcxt <*> view vals

evalM :: HasVals cxt Vals => Tm -> M cxt Val
evalM t = embedEvalM (eval t)

applyM :: HasVals cxt Vals => Closure -> Val -> M cxt Val
applyM t ~u = embedEvalM (apply t u)

fresh :: EvalM (Name -> Name)
fresh = do
  let go vs "_" = "_"
      go vs x = case lookup x vs of
        Just _  -> go vs (x ++ "'")
        Nothing -> x
  go <$> view vals

freshM :: HasVals cxt Vals => M cxt (Name -> Name)
freshM = embedEvalM fresh

quote :: Val -> EvalM Tm
quote = go where

  goBind :: Name -> Closure -> EvalM Tm
  goBind x t =
    local (vals %~ ((x, Nothing):)) (go =<< apply t (VVar x))

  go :: Val -> EvalM Tm
  go v = do
    fresh <- fresh
    force v >>= \case
      VNe h sp -> do
        let goSp :: Spine -> EvalM Tm
            goSp SNil = case h of
              HMeta x    -> pure $ Meta x
              HVar x     -> pure $ Var x
            goSp (SApp sp u i)    = App <$> goSp sp <*> go u <*> pure i
            goSp (SAppTel a sp u) = AppTel <$> go a <*> goSp sp <*> go u
            goSp (SProj1 sp)      = Proj1 <$> goSp sp
            goSp (SProj2 sp)      = Proj2 <$> goSp sp
        goSp sp

      VLam (fresh -> x) i t    -> Lam x i <$> goBind x t
      VPi (fresh -> x) i a b   -> Pi x i <$> go a <*> goBind x b
      VU                       -> pure U
      VTel                     -> pure Tel
      VRec a                   -> Rec <$> go a
      VTEmpty                  -> pure TEmpty
      VTCons (fresh -> x) a as -> TCons x <$> go a <*> goBind x as
      VTempty                  -> pure Tempty
      VTcons t u               -> Tcons <$> go t <*> go u
      VPiTel (fresh -> x) a b  -> PiTel x <$> go a <*> goBind x b
      VLamTel (fresh -> x) a t -> LamTel x <$> go a <*> goBind x t

quoteM :: HasVals cxt Vals => Val -> M cxt Tm
quoteM v = embedEvalM (quote v)

nf :: Tm -> EvalM Tm
nf t = quote =<< eval t

nfM :: HasVals cxt Vals => Tm -> M cxt Tm
nfM t = embedEvalM (nf t)
