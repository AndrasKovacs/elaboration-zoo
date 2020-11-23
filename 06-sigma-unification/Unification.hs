{-# options_ghc -Wno-unused-top-binds -Wno-unused-imports -Wno-type-defaults #-}

module Unification (unify, freshMeta) where

import Control.Exception
import Control.Monad
import Control.Monad.State.Strict hiding (lift)
import Data.IORef
import Lens.Micro.Platform
import Prelude hiding (exp)
import qualified Data.IntMap as IM

import Common
import Errors
import Evaluation
import Metacontext
import Syntax
import Value
import Cxt
import Pretty

import Debug.Trace

-- | Partial substitution from Γ to Δ. It is factored into a total substitution
--   from Δ' to Δ, and a partial substitution from Γ to Δ'. The total
--   substitution is an *eta expansion* of zero or more variables in Δ. In Δ',
--   the extra variables compared to Δ are *negative* levels. This allows us to
--   use fresh variable convention to insert new expansions
--   efficiently. However, these variables remain an internal implementation
--   detail, externally, a PartialSub from Γ to Δ still uses strict de Bruijn
--   convention.
data PartialSub = PSub {
    partialSubOcc    :: Maybe MetaVar  -- optional meta for occurs check
  , partialSubDom    :: Lvl            -- Γ
  , partialSubCod    :: Lvl            -- Δ
  , partialSubSub    :: IM.IntMap Val  -- Γ ~> Δ'
  , partialSubFresh  :: Lvl            -- fresh (negative) level for expansion insertion
  , partialSubExp    :: IM.IntMap Val  -- Δ' ~> Δ, eta expansion
  }
makeFields ''PartialSub

lift :: PartialSub -> PartialSub
lift (PSub occ dom cod sub fresh exp) =
  PSub occ (dom + 1) (cod + 1) (IM.insert (unLvl cod) (VVar dom) sub) fresh exp

skip :: PartialSub -> PartialSub
skip (PSub occ dom cod sub fresh exp) = PSub occ dom (cod + 1) sub fresh exp

forceWithExpansion :: PartialSub -> Val -> Val
forceWithExpansion psub t = case force t of
  VRigid x sp | Just v <- IM.lookup (coerce x) (psub^.exp) ->
    forceWithExpansion psub (vAppSp v sp)
  t -> t

idEnv :: Lvl -> Env
idEnv 0 = []
idEnv l = idEnv (l - 1) :> VVar (l - 1)

-- | Eta expand a codomain variable in a PartialSub.
etaExpandVar :: Lvl -> Lvl -> Spine -> PartialSub -> PartialSub
etaExpandVar gamma x sp psub = let

  freshVar :: Pruning -> State PartialSub Tm
  freshVar pr = do
    x <- fresh <<%= subtract 1
    pure $ AppPruning (Var (coerce x)) pr

  go :: Pruning -> Spine -> State PartialSub Tm
  go pr = \case
    SNil              -> freshVar pr
    SApp sp t i       -> Lam  "x" i <$> go (pr :> Just i) sp
    SProj1 sp         -> Pair <$> go pr sp <*> freshVar pr
    SProj2 sp         -> Pair <$> freshVar pr <*> go pr sp
    SProjField sp _ 0 -> Pair <$> freshVar pr <*> go pr sp
    SProjField sp x n -> Pair <$> go pr (SProjField sp x (n - 1)) <*> freshVar pr

  in case runState (go (replicate (coerce gamma) Nothing) (reverseSpine sp)) psub of
       (t, psub) -> psub & exp %~ IM.insert (coerce x) (eval (idEnv gamma) t)

--------------------------------------------------------------------------------

-- | Create a fresh meta with given type.
freshMeta :: Dbg => Cxt -> VTy -> IO Tm
freshMeta cxt a = do
  let ~closed = eval [] $ closeTy (path cxt) (quote (lvl cxt) a)
  m <- pushMeta closed
  pure $ AppPruning (Meta m) (pruning cxt)

-- | Eta expand a meta enough so that all projections disappear from the given spine.
etaExpandMeta :: MetaVar -> Spine -> IO ()
etaExpandMeta m sp = do
  a <- snd <$> lookupUnsolved m

  let go :: Cxt -> Spine -> VTy -> IO Tm
      go cxt sp a = case (sp, force a) of
        (SNil             , a          ) -> freshMeta cxt a
        (SApp sp t i      , VPi x _ a b) -> Lam x i <$> go (bind cxt x a) sp (b $$ VVar (lvl cxt))
        (SProj1 sp        , VSg x a b  ) -> do t <- go cxt sp a
                                               Pair t <$> freshMeta cxt (b $$ eval (env cxt) t)
        (SProj2 sp        , VSg x a b  ) -> do t <- freshMeta cxt a
                                               Pair t <$> go cxt sp (b $$ eval (env cxt) t)
        (SProjField sp _ 0, VSg x a b  ) -> do t <- go cxt sp a
                                               Pair t <$> freshMeta cxt (b $$ eval (env cxt) t)
        (SProjField sp x n, VSg _ a b  ) -> do sp <- pure $ SProjField sp x (n - 1)
                                               t <- freshMeta cxt a
                                               Pair t <$> go cxt sp (b $$ eval (env cxt) t)
        _                                -> impossible

  m' <- go (emptyCxt (initialPos "")) (reverseSpine sp) a
  solve' m (PSub (Just m) 0 0 mempty (-1) mempty) (eval [] m')

solve :: Dbg => Lvl -> MetaVar -> Spine -> Val -> IO ()
solve gamma m sp rhs = do
  traceShowM ("solve"::String, quote gamma (VFlex m sp), quote gamma rhs)
  try @UnifyError (invertSp 0 gamma gamma 0 sp) >>= \case
    Left NeedExpansion -> etaExpandMeta m sp >> unify gamma (VFlex m sp) rhs
    Left e             -> throwIO e
    Right psub         -> solve' m psub rhs

-- | Solve m given the result of inversion on a spine.
solve' :: Dbg => MetaVar -> PartialSub -> Val -> IO ()
solve' m psub rhs = do
  traceShowM ("solve'"::String, m, IM.keys (psub^.sub), IM.keys (psub^.exp), (forceWithExpansion psub rhs))
  (mlink, mty) <- lookupUnsolved m
  rhs <- psubst (psub & occ .~ Just m) rhs
  let solution = eval [] $ lams (psub^.dom) mty rhs
  modifyIORef' mcxt $ IM.insert (coerce m) (Solved mlink solution mty)

psubstSp :: Dbg => PartialSub -> Tm -> Spine -> IO Tm
psubstSp psub t = \case
  SNil              -> pure t
  SApp sp u i       -> App <$> psubstSp psub t sp <*> psubst psub u <*> pure i
  SProj1 sp         -> Proj1 <$> psubstSp psub t sp
  SProj2 sp         -> Proj2 <$> psubstSp psub t sp
  SProjField sp x n -> ProjField <$> psubstSp psub t sp <*> pure x <*> pure n

psubst :: Dbg => PartialSub -> Val -> IO Tm
psubst psub t = case forceWithExpansion psub t of
  VFlex m' sp -> do
    case psub^.occ of
      Nothing ->
        psubstSp psub (Meta m') sp
      Just m -> case compareMetas m m' of
        EQ -> throwIO UnifyError
        LT -> do
          mty' <- case lookupMeta m' of Unsolved _ a -> pure a; _ -> impossible
          mty' <- psubst (PSub (Just m) 0 0 mempty (-1) mempty) mty'
          strengthenMeta m m' (eval [] mty')
          psubstSp psub (Meta m') sp
        GT -> do
          psubstSp psub (Meta m') sp

  VRigid (Lvl x) sp -> case IM.lookup x (psub^.sub) of
    Nothing -> throwIO UnifyError
    Just x' -> psubstSp psub (quote (psub^.dom) x') sp

  VLam x i t  -> Lam x i <$> psubst (lift psub) (t $$ VVar (psub^.cod))
  VPi x i a b -> Pi x i <$> psubst psub a <*> psubst (lift psub) (b $$ VVar (psub^.cod))
  VSg x a b   -> Sg x <$> psubst psub a <*> psubst (lift psub) (b $$ VVar (psub^.cod))
  VPair t u   -> Pair <$> psubst psub t <*> psubst psub u
  VU          -> pure U

invertVal :: Dbg => Lvl -> Lvl -> Lvl -> Val -> Spine -> PartialSub -> IO PartialSub
invertVal gammau gammas gammap t rhsSp psub = go gammap t rhsSp psub where

  lams :: Spine -> Tm -> Tm
  lams SNil          t = t
  lams (SApp sp _ i) t = lams sp (Lam "x" i t)
  lams _             _ = impossible

  go :: Dbg => Lvl -> Val -> Spine -> PartialSub -> IO PartialSub
  go gammap t rhsSp psub = case forceWithExpansion psub t of

    VRigid x sp -> do
      -- x is not solvable
      when ((0 <= x && x < gammau) || (gammas <= x && x < gammap)) $ throwIO UnifyError
      -- x is nonlinear
      when (IM.member (coerce x) (psub^.sub))                      $ throwIO UnifyError

      try @UnifyError (invertSp gammas gammap gammap (psub^.dom) sp) >>= \case
        Right spInv -> do
          rhs <- psubstSp spInv (Var (Ix (spineLen sp))) rhsSp
          traceShowM ("invert param", x, psub^.dom, lams sp rhs)
          pure $ psub & sub %~ IM.insert (coerce x) (eval (idEnv (psub^.dom)) (lams sp rhs))
        Left NeedExpansion -> do
          traceShowM ("var expansion needed", quote gammap (VRigid x sp))
          psub <- pure $ etaExpandVar gammap x sp psub
          traceShowM ("var expanded", x, quote gammap $ forceWithExpansion psub (VRigid x SNil),
                     quote gammap $ forceWithExpansion psub (VRigid x sp))
          go gammap (VRigid x sp) rhsSp psub
        Left e ->
          throwIO e

    VPair t u -> do
      psub <- go gammap t (SProj1 rhsSp) psub
      go gammap u (SProj2 rhsSp) psub

    VLam x i t ->
      go (gammap + 1) (t $$ VVar gammap) (SApp rhsSp (VVar gammap) i) psub

    _ ->
      throwIO UnifyError

invertSp :: Dbg => Lvl -> Lvl -> Lvl -> Lvl -> Spine -> IO PartialSub
invertSp gammau gammas gammap delta sp = go sp where
  go :: Spine -> IO PartialSub
  go SNil =
    pure (PSub Nothing delta gammas mempty (-1) mempty)
  go (SApp sp t i) = do
    spInv <- (dom +~ 1) <$> go sp
    invertVal gammau gammas gammap t SNil spInv
  go _ =
    throwIO NeedExpansion

-- | Wrap a term in Lvl number of lambdas. We get the domain info from the
--   VTy argument.
lams :: Dbg => Lvl -> VTy -> Tm -> Tm
lams l a t = go a (0 :: Lvl) where
  go a l' | l' == l = t
  go a l' = case force a of
    VPi "_" i a b -> Lam ("x"++show l') i $ go (b $$ VVar l') (l' + 1)
    VPi x i a b   -> Lam x i $ go (b $$ VVar l') (l' + 1)
    _             -> impossible

unifyProjField :: Dbg => Lvl -> Spine -> (Spine, Int) -> IO ()
unifyProjField l sp (!sp', !n) = case (sp, sp', n) of
  (sp,        sp', 0) -> unifySp l sp sp'
  (SProj2 sp, sp', n) -> unifyProjField l sp (sp', n - 1)
  _                   -> throwIO UnifyError

unifySp :: Dbg => Lvl -> Spine -> Spine -> IO ()
unifySp l sp sp' = case (sp, sp') of
  (SNil              , SNil               ) -> pure ()
  (SApp sp t _       , SApp sp' t' _      ) -> unifySp l sp sp' >> unify l t t'
  (SProj1 sp         , SProj1 sp'         ) -> unifySp l sp sp'
  (SProj2 sp         , SProj2 sp'         ) -> unifySp l sp sp'
  (SProjField sp _ n , SProjField sp' _ n') -> unifySp l sp sp' >> unless (n == n') (throwIO UnifyError)
  (SProjField sp _ n , SProj1 sp'         ) -> unifyProjField l sp' (sp, n)
  (SProj1 sp         , SProjField sp' _ n') -> unifyProjField l sp (sp', n')
  _                                         -> throwIO UnifyError

flexFlex :: Dbg => Lvl -> MetaVar -> Spine -> MetaVar -> Spine -> IO ()
flexFlex gamma m sp m' sp'
  | spineLen sp < spineLen sp' = flexFlex gamma m' sp' m sp
flexFlex gamma m sp m' sp' =
  try @UnifyError (invertSp 0 gamma gamma 0 sp) >>= \case
    Left NeedExpansion -> do
      etaExpandMeta m sp
      unify gamma (VFlex m sp) (VFlex m' sp')
    Left _ -> do
      try @UnifyError (invertSp 0 gamma gamma 0 sp') >>= \case
        Left NeedExpansion -> etaExpandMeta m' sp' >> unify gamma (VFlex m sp) (VFlex m' sp')
        Left e             -> throwIO e
        Right psub         -> solve' m' psub (VFlex m sp)
    Right psub -> do
      solve' m psub (VFlex m' sp')

unify :: Dbg => Lvl -> Val -> Val -> IO ()
unify l t u = case (force t, force u) of
  (VU         , VU             ) -> pure ()
  (VPi x i a b, VPi x' i' a' b') | i == i' -> unify l a a' >> unify (l + 1) (b $$ VVar l) (b' $$ VVar l)
  (VSg x a b  , VSg x' a' b'   )           -> unify l a a' >> unify (l + 1) (b $$ VVar l) (b' $$ VVar l)
  (VRigid x sp, VRigid x' sp'  ) | x == x' -> unifySp l sp sp'
  (VFlex m sp , VFlex m' sp'   ) | m == m' -> unifySp l sp sp' -- intersection
  -- (VFlex m sp , VFlex m' sp'   )           -> flexFlex l m sp m' sp'

  (VLam _ _ t , VLam _ _ t'    ) -> unify (l + 1) (t $$ VVar l) (t' $$ VVar l)
  (t          , VLam _ i t'    ) -> unify (l + 1) (vApp t (VVar l) i) (t' $$ VVar l)
  (VLam _ i t , t'             ) -> unify (l + 1) (t $$ VVar l) (vApp t' (VVar l) i)

  (VPair t u  , VPair t' u'    ) -> unify l t t' >> unify l u u'
  (VPair t u  , t'             ) -> unify l t (vProj1 t') >> unify l u (vProj2 t')
  (t          , VPair t' u'    ) -> unify l (vProj1 t) t' >> unify l (vProj2 t) u'

  (VFlex m sp , t'             ) -> solve l m sp t'
  (t          , VFlex m' sp'   ) -> solve l m' sp' t
  _                              -> throwIO UnifyError
