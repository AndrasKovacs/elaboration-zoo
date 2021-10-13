{-# options_ghc -Wno-unused-top-binds -Wno-unused-imports -Wno-type-defaults #-}

module Unification (unify, freshMeta) where

import Control.Exception
import Control.Monad
import Control.Monad.State.Strict hiding (lift)
import Data.IORef
import Lens.Micro.Platform
import Prelude hiding (exp, curry)
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

--------------------------------------------------------------------------------

-- | Partial substitution from Γ to Δ. It is factored into a total substitution
--   from Δ' to Δ, and a partial substitution from Γ to Δ'. The total
--   substitution is an *eta expansion* of zero or more variables in Δ. In Δ',
--   the extra variables compared to Δ are *negative* levels. This allows us to
--   use fresh variable convention to insert new expansions
--   efficiently. However, these variables remain an internal implementation
--   detail, externally, a PartialSub from Γ to Δ still uses strict de Bruijn
--   convention.
data PartialSub = PSub {
    partialSubOcc      :: Maybe MetaVar  -- optional meta for occurs check
  , partialSubDom      :: Lvl            -- Γ
  , partialSubCod      :: Lvl            -- Δ
  , partialSubSub      :: IM.IntMap Val  -- Γ ~> Δ'
  , partialSubFresh    :: Lvl            -- fresh (negative) level for expansion insertion (Δ')
  , partialSubExp      :: IM.IntMap Val  -- Δ' ~> Δ, eta expansion
  , partialSubIsLinear :: Bool           -- is the partial substitution linear? If not,
  }                                      -- we have to check that the rhs type is valid
                                         -- after substitution
makeFields ''PartialSub

--     f      η-exp
-- Γ   →   Δ'  →    Δ

emptyPSub :: PartialSub
emptyPSub = PSub Nothing 0 0 mempty (-1) mempty True

lift :: PartialSub -> PartialSub
lift (PSub occ dom cod sub fresh exp lin) =
  PSub occ (dom + 1) (cod + 1) (IM.insert (unLvl cod) (VVar dom) sub) fresh exp lin

skip :: PartialSub -> PartialSub
skip = cod +~ 1

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

-- | Create a fresh eta-expanded value for a meta such that applying it to the spine returns
--   a VFlex without projections.
metaExpansion :: MetaVar -> Spine -> IO Val
metaExpansion m sp = do
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

  eval [] <$> go (emptyCxt (initialPos "")) (reverseSpine sp) a

-- | Expand a meta, eliminating projections from the spine. Also update the meta with the expansion.
expandMeta :: MetaVar -> Spine -> IO Val
expandMeta m sp = do
  m' <- metaExpansion m sp
  solve' m SNil emptyPSub m'
  pure $! vAppSp m' sp

p2name :: Name -> Name
p2name "_" = "_"
p2name x = x ++ "2"

-- | Curry a type enough so that all nested pairs disappear from the given spine.
curry :: PartialSub -> Spine -> VTy -> VTy
curry psub sp a = go (reverseSpine sp) a where
  go :: Spine -> VTy -> VTy
  go (SApp sp t i) a = case (forceWithExpansion psub t, force a) of
    (VPair t u, VPi x i (VSg y a b) c) ->
      go (SApp (SApp sp u i) t i)
         (VPi y i a $ Fun \a -> VPi (p2name x) i (b $$ a) $ Fun \b -> c $$ VPair a b)
    (t , VPi x i a b) ->
      VPi x i a $ Fun \x -> go sp (b $$ x)
    _ ->
      impossible
  go _ a = a

-- | Transport a value from (Curry A) to A.
fromCurry :: PartialSub -> Spine -> Val -> Val
fromCurry psub sp t = go (reverseSpine sp) t where
  go :: Spine -> Val -> Val
  go (SApp sp t i) v = case forceWithExpansion psub t of
    VPair t u ->
      VLam "x" i $ Fun \x ->
        vApp (vApp (go (SApp (SApp sp u i) t i) v) (vProj1 x) i) (vProj2 x) i
    _ ->
      VLam "x" i $ Fun \x -> go sp (vApp v x i)
  go _ v = v

-- | Try to eliminate pairs and projections from spine.
prunePrep :: PartialSub -> MetaVar -> Spine -> IO (MetaVar, Spine)
prunePrep psub m sp = do

  -- prep
  let (needsCurry, needsExpansion) = go (False, False) sp where
        go (!curry, !exp) = \case
          SNil              -> (curry, exp)
          SApp sp t _       -> case forceWithExpansion psub t of
                                 VPair{} -> go (True , exp) sp
                                 _       -> go (curry, exp) sp
          SProj1 sp         -> go (curry, True) sp
          SProj2 sp         -> go (curry, True) sp
          SProjField sp _ _ -> go (curry, True) sp

  (m, sp) <- if needsExpansion then do
               VFlex m sp <- expandMeta m sp
               pure (m, sp)
             else
               pure (m, sp)

  if needsCurry then do
    a <- snd <$> lookupUnsolved m
    let ca = curry psub sp a
    m' <- fromCurry psub sp . VMeta <$> pushMeta ca
    solve' m SNil emptyPSub m'
    case vAppSp m' sp of
      VFlex m sp -> pure (m, sp)
      _          -> impossible

  else do
    pure (m, sp)

-- | Remove some arguments from a closed iterated Pi type.
pruneTy :: RevPruning -> VTy -> IO Ty
pruneTy (RevPruning pr) a = go pr emptyPSub a where
  go :: Pruning -> PartialSub -> VTy -> IO Ty
  go pr psub a = case (pr, force a) of
    ([]          , a          ) -> psubst psub a
    (Just{}  : pr, VPi x i a b) -> Pi x i <$> psubst psub a
                                          <*> go pr (lift psub) (b $$ VVar (psub^.cod))
    (Nothing : pr, VPi x i a b) -> go pr (skip psub) (b $$ VVar (psub^.cod))
    _                           -> impossible

-- | Prune arguments from a meta, return new meta + pruned type.
pruneMeta :: Pruning -> MetaVar -> IO (MetaVar, VTy)
pruneMeta pruning m = do

  (mlink, mty) <- lookupUnsolved m

  prunedty <- eval [] <$> pruneTy (revPruning pruning) mty

  m' <- pushMeta prunedty
  strengthenMeta m m' prunedty

  let solution = eval [] $ lams (Lvl $ length pruning) mty $ AppPruning (Meta m') pruning
  modifyIORef' mcxt $ IM.insert (coerce m) (Solved mlink solution mty)
  pure (m', prunedty)


data SpinePruneStatus
  = OKRenaming    -- ^ Valid spine which is a renaming
  | OKNonRenaming -- ^ Valid spine but not a renaming (has a non-var entry)
  | NeedsPruning  -- ^ A spine which is a renaming and has out-of-scope var entries

-- | Prune illegal var occurrences from a meta + spine.
--   Returns: renamed + pruned term, head meta after pruning, type of the head meta after pruning.
pruneVFlex :: PartialSub -> MetaVar -> Spine -> IO Tm
pruneVFlex psub m sp = do
  -- traceShowM ("try pruning", m, sp)

  (sp :: [(Maybe Tm, Icit)], status :: SpinePruneStatus) <- let
    go SNil          = pure ([], OKRenaming)
    go (SApp sp t i) = do
      (sp, status) <- go sp
      case forceWithExpansion psub t of
        VVar x -> case (IM.lookup (coerce x) (psub^.sub), status) of
                    (Just x , _            ) -> pure ((Just (quote (psub^.dom) x), i) : sp, status)
                    (Nothing, OKNonRenaming) -> throwIO UnifyError
                    (Nothing, _            ) -> pure ((Nothing, i):sp, NeedsPruning)
        t      -> case status of
                    NeedsPruning -> throwIO UnifyError
                    _            -> do {t <- psubst psub t; pure ((Just t, i):sp, OKNonRenaming)}
    go _ = throwIO UnifyError

    in go sp

  (m', mty') <- case status of
    OKRenaming    -> do {a <- snd <$> lookupUnsolved m; pure (m, a)}
    OKNonRenaming -> do {a <- snd <$> lookupUnsolved m; pure (m, a)}
    NeedsPruning  -> pruneMeta (map (\(mt, i) -> i <$ mt) sp) m

  pure $! foldr (\(mu, i) t -> maybe t (\u -> App t u i) mu) (Meta m') sp

--------------------------------------------------------------------------------

-- curry0 = curry emptyPSub
-- fromCurry0 = fromCurry emptyPSub
-- shew = putStrLn . showTm0 . quote 0

vProd a b = VSg "_" a $ Fun \_ -> b
vFun a b = VPi "_" Expl a $ Fun \_ -> b

-- ty1 = VPi "AB" Expl (VSg "A" VU $ Fun \a -> a) $ Fun \ab -> vFun (vProj1 ab) (vProj1 ab)
-- ty2 = vFun (vProd (vProd VU VU) (vProd (vProd VU VU) VU)) VU
-- tm1 = VLam "A" Expl $ Fun \a -> VLam "x" Expl $ Fun \x -> VLam "y" Expl $ Fun \y -> x
-- tm2 = VLam "a" Expl $ Fun \a -> VLam "b" Expl $ Fun \b -> VLam "c" Expl $ Fun \c ->
--       VLam "d" Expl $ Fun \d ->  VPair a $ VPair b $ VPair c d

--------------------------------------------------------------------------------


solve :: Dbg => Lvl -> MetaVar -> Spine -> Val -> IO ()
solve gamma m sp rhs = do
  -- traceShowM ("solve"::String, quote gamma (VFlex m sp), quote gamma rhs)
  try @UnifyError (invertSp 0 gamma gamma 0 sp) >>= \case
    Left NeedExpansion -> do msp <- expandMeta m sp
                             unify gamma msp rhs
    Left e             -> throwIO e
    Right psub         -> solve' m sp psub rhs

validateRhsType :: VTy -> Spine -> PartialSub -> IO ()
validateRhsType mty sp psub = do
  let getTy :: VTy -> Spine -> VTy
      getTy a             SNil          = a
      getTy (VPi x i a b) (SApp sp t _) = getTy (b $$ t) sp
      getTy _             _             = impossible
  let rhsTy = getTy mty (reverseSpine sp)
  -- traceShowM ("rhsTy", rhsTy, psub^.sub&IM.keys, psub^.exp&IM.keys, sp)
  rhsTy <- psubst psub rhsTy
  pure ()

-- | Solve m given the result of inversion on a spine.
solve' :: Dbg => MetaVar -> Spine -> PartialSub -> Val -> IO ()
solve' m sp psub rhs = do

  -- traceShowM ("solve'"::String, m, IM.keys (psub^.sub), IM.keys (psub^.exp), (forceWithExpansion psub rhs))
  (mlink, mty) <- lookupUnsolved m

  when (not $ psub^.isLinear) $ do
    validateRhsType mty sp psub

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

psubstSpWithPruning :: PartialSub -> MetaVar -> Spine -> IO Tm
psubstSpWithPruning psub m sp =
  try (psubstSp psub (Meta m) sp) >>= \case
    Left NeedExpansion ->
      impossible
    Left UnifyError -> do
      (m, sp) <- prunePrep psub m sp
      t <- pruneVFlex psub m sp
      pure t
    Right t -> do
      pure t

psubst :: Dbg => PartialSub -> Val -> IO Tm
psubst psub t = case forceWithExpansion psub t of

  VFlex m' sp -> do
    case psub^.occ of
      Nothing -> do
        psubstSpWithPruning psub m' sp
      Just m | m == m'   -> throwIO UnifyError -- occurs check
             | otherwise -> psubstSpWithPruning psub m' sp

  VRigid (Lvl x) sp -> case IM.lookup x (psub^.sub) of
    Nothing -> throwIO UnifyError -- scope error
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

      -- x is non-linear
      if IM.member (coerce x) (psub^.sub) then do
        pure $ psub
          & isLinear .~ False
          & sub      %~ IM.delete (coerce x)

      -- x is linear
      else do
        try @UnifyError (invertSp gammas gammap gammap (psub^.dom) sp) >>= \case
          Right spInv -> do
            rhs <- psubstSp spInv (Var (Ix (spineLen sp))) rhsSp
            pure $ psub & sub %~ IM.insert (coerce x) (eval (idEnv (psub^.dom)) (lams sp rhs))
          Left NeedExpansion -> do
            psub <- pure $ etaExpandVar gammap x sp psub
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
    pure (PSub Nothing delta gammas mempty (-1) mempty True)
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
      msp <- expandMeta m sp
      unify gamma msp (VFlex m' sp')
    Left _ -> do
      try @UnifyError (invertSp 0 gamma gamma 0 sp') >>= \case
        Left NeedExpansion -> do msp' <- expandMeta m' sp'
                                 unify gamma (VFlex m sp) msp'
        Left e             -> throwIO e
        Right psub         -> solve' m' sp' psub (VFlex m sp)
    Right psub -> do
      solve' m sp psub (VFlex m' sp')

unify :: Dbg => Lvl -> Val -> Val -> IO ()
unify l t u = case (force t, force u) of
  (VU         , VU             ) -> pure ()
  (VPi x i a b, VPi x' i' a' b') | i == i' -> unify l a a' >> unify (l + 1) (b $$ VVar l) (b' $$ VVar l)
  (VSg x a b  , VSg x' a' b'   )           -> unify l a a' >> unify (l + 1) (b $$ VVar l) (b' $$ VVar l)
  (VRigid x sp, VRigid x' sp'  ) | x == x' -> unifySp l sp sp'
  (VFlex m sp , VFlex m' sp'   ) | m == m' -> unifySp l sp sp' -- intersection
  (VFlex m sp , VFlex m' sp'   )           -> flexFlex l m sp m' sp'

  (VLam _ _ t , VLam _ _ t'    ) -> unify (l + 1) (t $$ VVar l) (t' $$ VVar l)
  (t          , VLam _ i t'    ) -> unify (l + 1) (vApp t (VVar l) i) (t' $$ VVar l)
  (VLam _ i t , t'             ) -> unify (l + 1) (t $$ VVar l) (vApp t' (VVar l) i)

  (VPair t u  , VPair t' u'    ) -> unify l t t' >> unify l u u'
  (VPair t u  , t'             ) -> unify l t (vProj1 t') >> unify l u (vProj2 t')
  (t          , VPair t' u'    ) -> unify l (vProj1 t) t' >> unify l (vProj2 t) u'

  (VFlex m sp , t'             ) -> solve l m sp t'
  (t          , VFlex m' sp'   ) -> solve l m' sp' t
  _                              -> throwIO UnifyError
