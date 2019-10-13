
module Evaluation (
    apply
  , applyM
  , close
  , closeM
  , eval
  , evalM
  , force
  , forceM
  , forceSp
  , forceSpM
  , fresh
  , hlamM
  , nf
  , nfM
  , quote
  , quoteM
  , runEval
  , vApp
  , vAppM
  , zonk
  , zonkM
  ) where

import Control.Monad.Reader
import Lens.Micro.Platform
import qualified Data.IntMap.Strict as M

import Types

--------------------------------------------------------------------------------

runEval :: EvalM a -> MCxt -> Vals -> a
runEval ma ms vs = runReader ma (EvalEnv ms vs)

embedEvalM :: HasVals cxt Vals => EvalM a -> M cxt a
embedEvalM ma = runEval ma <$> use mcxt <*> view vals

vProj1 :: Val -> EvalM Val
vProj1 (VTcons t u)    = pure t
vProj1 (VNe h sp)      = pure $ VNe h (SProj1 sp)
vProj1 (VLamTel x a t) = vProj1 =<< vLamTel pure x a t
vProj1 _               = error "impossible"

vProj2 :: Val -> EvalM Val
vProj2 (VTcons t u)    = pure u
vProj2 (VNe h sp)      = pure $ VNe h (SProj2 sp)
vProj2 (VLamTel x a t) = vProj2 =<< vLamTel pure x a t
vProj2 _               = error "impossible"

vVar :: Name -> EvalM Val
vVar x = do
  vs <- view vals
  case (lookup x vs) of
    Nothing -> pure (VVar x) -- error $ "impossible: " ++ x ++ " not in scope"
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

hlamM :: HasVals cxt Vals => (Val -> EvalM Val) -> M cxt Closure
hlamM t = embedEvalM (hlam t)

close :: Name -> Tm -> EvalM Closure
close x t = hlam (\ ~v -> defining x v $ eval t)

closeM :: HasVals cxt Vals => Name -> Tm -> M cxt Closure
closeM x t = embedEvalM (close x t)

apply :: Closure -> Val -> EvalM Val
apply cl ~u = cl <$> view mcxt <*> pure u

applyM :: HasVals cxt Vals => Closure -> Val -> M cxt Val
applyM t ~u = embedEvalM (apply t u)

vAppSp :: Val -> Spine -> EvalM Val
vAppSp h = go where
  go SNil             = pure h
  go (SApp sp u i)    = do {sp <- go sp; vApp sp u i}
  go (SAppTel a sp u) = do {sp <- go sp; vAppTel a sp u}
  go (SProj1 sp)      = vProj1 =<< go sp
  go (SProj2 sp)      = vProj2 =<< go sp

-- | Force the outermost constructor in a value. Does not force the spine
--   of a neutral value.
force :: Val -> EvalM Val
force = \case
  v@(VNe (HMeta m) sp) -> lookupMeta m >>= \case
    Unsolved{} -> pure v
    Solved v   -> force =<< vAppSp v sp
    _          -> error "impossible"

  VPiTel x a b  -> vPiTel force x a b
  VLamTel x a t -> vLamTel force x a t
  v             -> pure v

forceM :: HasVals cxt Vals => Val -> M cxt Val
forceM v = embedEvalM (force v)

-- | Force a spine, computing telescope applications where possible.
forceSp :: Spine -> EvalM Spine
forceSp sp = vAppSp (VVar "_") sp >>= \case
  VNe _ sp -> pure sp
  _        -> error "impossible"

forceSpM :: HasVals cxt Vals => Spine -> M cxt Spine
forceSpM sp = embedEvalM (forceSp sp)

-- We parameterize vPiTel and vLamTel with a continuation, because
-- sometimes we additionally want to force the result.
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
vAppTel a t ~u =
  force a >>= \case
    VTEmpty       -> pure t
    VTCons _ a as -> do
      ~v1 <- vProj1 u
      join (vAppTel <$> apply as v1 <*> vApp t v1 Impl <*> vProj2 u)
    a -> case t of
      VLamTel _ _ t -> apply t u
      VNe h sp      -> pure $ VNe h (SAppTel a sp u)
      _             -> error "impossible"

vApp :: Val -> Val -> Icit -> EvalM Val
vApp (VLam _ _ t   ) ~u i = apply t u
vApp (VNe h sp     ) ~u i = pure $ VNe h (SApp sp u i)
vApp (VLamTel x a t) ~u i = do {t <- vLamTel pure x a t; vApp t u i}
vApp _                _ _ = error "impossible"

vAppM :: HasVals cxt Vals => Val -> Val -> Icit -> M cxt Val
vAppM t ~u i = embedEvalM (vApp t u i)

eval :: Tm -> EvalM Val
eval t = go t where
  go :: Tm -> EvalM Val
  go = \case
    Var x        -> vVar x
    Let x _ t u  -> do {~v <- go t; defining x v $ go u}
    Assume x _ t -> local (vals %~ ((x, Nothing):)) $ go t
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
    Proj1 t      -> vProj1 =<< go t
    Proj2 t      -> vProj2 =<< go t
    PiTel x a b  -> join (vPiTel pure x <$> go a <*> close x b)
    AppTel a t u -> join (vAppTel <$> go a <*> go t <*> go u)
    LamTel x a t -> join (vLamTel pure x <$> go a <*> close x t)

evalM :: HasVals cxt Vals => Tm -> M cxt Val
evalM t = embedEvalM (eval t)

fresh :: Vals -> Name -> Name
fresh vs "_" = "_"
fresh vs x = case lookup x vs of
  Just _  -> fresh vs (x ++ "'")
  Nothing -> x

quote :: Val -> EvalM Tm
quote = go where

  goBind :: Name -> Closure -> EvalM Tm
  goBind x t =
    local (vals %~ ((x, Nothing):)) (go =<< apply t (VVar x))

  go :: Val -> EvalM Tm
  go v = do
    fresh <- fresh <$> view vals
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
        goSp =<< forceSp sp

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


--------------------------------------------------------------------------------

-- | Inlines meta solutions but does not compute telescopes.
zonk :: Tm -> EvalM Tm
zonk = go where

  goSp :: Tm -> EvalM (Either Val Tm)
  goSp = \case
    Meta m       -> lookupMeta m >>= \case
                      Solved v -> pure $ Left v
                      _        -> pure $ Right (Meta m)
    App t u ni   -> goSp t >>= \case
                      Left t  -> do {u <- eval u; Left <$> vApp t u ni}
                      Right t -> do {u <- go u; pure $ Right $ App t u ni}
    AppTel a t u -> goSp t >>= \case
                      Left t  -> do {a <- eval a; u <- eval u; Left <$> vAppTel a t u}
                      Right t -> do {a <- go a; u <- go u; pure $ Right $ AppTel a t u}
    t            -> Right <$> go t

  goBind :: Name -> Tm -> EvalM Tm
  goBind x t = local (vals %~ ((x, Nothing):)) (go t)

  go :: Tm -> EvalM Tm
  go = \case
    Var x        -> pure $ Var x
    Meta m       -> lookupMeta m >>= \case
                      Solved v   -> quote v
                      Unsolved{} -> pure (Meta m)
                      _          -> error "impossible"
    U            -> pure U
    Pi x i a b   -> Pi x i <$> go a <*> goBind x b
    App t u ni   -> goSp t >>= \case
                      Left t  -> do {u <- eval u; quote =<< vApp t u ni}
                      Right t -> do {u <- go u; pure $ App t u ni}
    Lam x i t    -> Lam x i <$> goBind x t
    Let x a t u  -> Let x <$> go a <*> go t <*> goBind x u
    Assume x a t -> Assume x <$> go a <*> goBind x t
    Tel          -> pure Tel
    TEmpty       -> pure TEmpty
    TCons x t u  -> TCons x <$> go t <*> goBind x u
    Rec a        -> Rec <$> go a
    Tempty       -> pure Tempty
    Tcons t u    -> Tcons <$> go t <*> go u
    Proj1 t      -> Proj1 <$> go t
    Proj2 t      -> Proj2 <$> go t
    PiTel x a b  -> PiTel x <$> go a <*> goBind x b
    AppTel a t u -> goSp t >>= \case
                      Left t  -> do {a <- eval a; u <- eval u; quote =<< vAppTel a t u}
                      Right t -> do {a <- go a; u <- go u; pure $ AppTel a t u}
    LamTel x a b -> LamTel x <$> go a <*> goBind x b

zonkM :: HasVals cxt Vals => Tm -> M cxt Tm
zonkM t = embedEvalM (zonk t)
