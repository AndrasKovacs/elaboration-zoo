
module Unification (unify, freshMeta) where

import Prelude hiding (curry)
import Control.Monad
import Control.Exception
import Data.IORef
import qualified Data.IntMap as IM

import Common
import Errors
import Evaluation
import Metacontext
import Syntax
import Value
import Cxt
-- import Pretty

-- Meta currying
--------------------------------------------------------------------------------

-- curry : U -> U
curry :: VTy -> VTy
curry (force -> VPi x i (force -> VSg y a b) c) =
  VPi y i a $ Fun \a -> curry $ VPi (x++"2") i (b $$ a) $ Fun \b -> c $$ VPair a b

  -- homework: implement without Fun
  -- curry ((x : (a : A) × B a) → C x) = (a : A) → curry ((b : B a) → C (a, b))
curry (force -> a) =
  a

-- What's the problem with AC?
--   we need matching under a binder (general problem in HOAS)
-- AC ((a : A) → (b : B a) × C a b) = ((b : (a : A) → B a) × ((a : A) → C a (b a)))
-- case (b $$ VVar lvl) of
--   VSg x a b -> .... closeVal ....

-- (related issue: NbE for cubical type theory)
--    (cubical TT: some computation rules require closeVal)
--    (Mörtberg et al : cubicallt : uses NbE only for normal values, and uses naive substitution for intervals)



-- fromCurry : (A : U) → curry A → A
fromCurry :: VTy -> Val -> Val
fromCurry (force -> VPi x i (force -> VSg y a b) c) t =

  -- t    : (a : A) → curry ((b : B a) → C (a, b))
  -- goal : (ab : (a : A) × B a) → C ab

  -- λ ab.
  --    t ab.1 : curry ((b : B ab.1) → C (ab.1, b))
  --    fromCurry ((b : B ab.1) → C (ab.1, b)) (t ab.1) : (b : B ab.1) → C (ab.1, b)
  --    fromCurry ((b : B ab.1) → C (ab.1, b)) (t ab.1) ab.2 : C (ab.1, ab.2)

  -- t ↦ λ ab. fromCurry ((b : B ab.1) → C (ab.1, b)) (t ab.1) ab.2

  VLam x i $ Fun \ab ->
    vApp (fromCurry (VPi (x++"2") i (b $$ vProj1 ab) $ Fun \b -> c $$ VPair (vProj1 ab) b)
                    (vApp t (vProj1 ab) i))
         (vProj2 ab)
         i
fromCurry (force -> a) t =
  t

-- -- test:
-- vProd a b = VSg "_" a $ Fun \_ -> b
-- vFun a b = VPi "_" Expl a $ Fun \_ -> b

-- ty1 = VPi "AB" Expl (VSg "A" VU $ Fun \a -> a) $ Fun \ab -> vFun (vProj1 ab) (vProj1 ab)
-- tm1 = VLam "A" Expl $ Fun \a -> VLam "x" Expl $ Fun \x -> VLam "y" Expl $ Fun \y -> x


--------------------------------------------------------------------------------

-- | Create a fresh meta with given type.
freshMeta :: Cxt -> VTy -> IO Tm
freshMeta cxt a = do
  let ~closed = eval [] $ closeTy (path cxt) (quote (lvl cxt) a)
  m <- pushMeta closed
  pure $ AppPruning (Meta m) (pruning cxt)

-- | Create a fresh meta which is maximally expanded along Pi and Sg eta.
freshExpandedMeta :: Cxt -> VTy -> IO Tm
freshExpandedMeta cxt a = case force a of
  VSg x a b -> do
    t <- freshExpandedMeta cxt a
    u <- freshExpandedMeta cxt (b $$ eval (env cxt) t)
    pure (Pair t u)
  VPi x i a b -> do
    t <- freshExpandedMeta (bind cxt x a) (b $$ VVar (lvl cxt))
    pure (Lam x i t)
  a -> do
    freshMeta cxt a

etaExpandMeta :: MetaVar -> IO ()
etaExpandMeta m = do
  (link, a) <- case lookupMeta m of
    Unsolved link a -> pure (link, a)
    _               -> impossible
  let curried = curry a
  m' <- freshExpandedMeta (emptyCxt (initialPos "")) curried
  solveWithPRen m (PRen (Just m) 0 0 mempty, Nothing) (fromCurry a $ eval [] m')

--------------------------------------------------------------------------------

-- partial renaming from Γ to Δ
data PartialRenaming = PRen {
    occ :: Maybe MetaVar   -- optional occurs check
  , dom :: Lvl             -- size of Γ
  , cod :: Lvl             -- size of Δ
  , ren :: IM.IntMap Lvl}  -- mapping from Δ vars to Γ vars

-- lift : (σ : PRen Γ Δ) → PRen (Γ, x : A[σ]) (Δ, x : A)
lift :: PartialRenaming -> PartialRenaming
lift (PRen occ dom cod ren) = PRen occ (dom + 1) (cod + 1) (IM.insert (unLvl cod) dom ren)

-- skip : PRen Γ Δ → PRen Γ (Δ, x : A)
skip :: PartialRenaming -> PartialRenaming
skip (PRen occ dom cod ren) = PRen occ dom (cod + 1) ren

-- | invert : (Γ : Cxt) → (spine : Sub Δ Γ) → PRen Γ Δ
--   Optionally returns a pruning of nonlinear spine entries, if there's any.
invert :: Lvl -> Spine -> IO (PartialRenaming, Maybe Pruning)
invert gamma sp = do

  let go :: Spine -> IO (Lvl, IM.IntMap Lvl, Pruning, Bool)
      go SNil =
        pure (0, mempty, [], True)
      go (SApp sp t i) = do
        (dom, ren, pr, isLinear) <- go sp
        case force t of
          VVar (Lvl x) -> case IM.member x ren of
            True  -> pure (dom + 1, IM.delete x ren    , Nothing : pr, False   )
            False -> pure (dom + 1, IM.insert x dom ren, Just i  : pr, isLinear)

          VPair{}               -> throwIO NeedExpansion
          -- VRigid _ SProj1{}     -> throwIO NeedExpansion
          -- VRigid _ SProj2{}     -> throwIO NeedExpansion
          -- VRigid _ SProjField{} -> throwIO NeedExpansion
          _                     -> throwIO UnifyError

      go SProj1{}     = throwIO NeedExpansion
      go SProj2{}     = throwIO NeedExpansion
      go SProjField{} = throwIO NeedExpansion

  (dom, ren, pr, isLinear) <- go sp
  pure (PRen Nothing dom gamma ren, pr <$ guard isLinear)


-- | Remove some arguments from a closed iterated Pi type.
pruneTy :: RevPruning -> VTy -> IO Ty
pruneTy (RevPruning pr) a = go pr (PRen Nothing 0 0 mempty) a where
  go pr pren a = case (pr, force a) of
    ([]          , a          ) -> rename pren a
    (Just{}  : pr, VPi x i a b) -> Pi x i <$> rename pren a
                                          <*> go pr (lift pren) (b $$ VVar (cod pren))
    (Nothing : pr, VPi x i a b) -> go pr (skip pren) (b $$ VVar (cod pren))
    _                           -> impossible

-- | Prune arguments from a meta, return new meta + pruned type.
pruneMeta :: Pruning -> MetaVar -> IO (MetaVar, VTy)
pruneMeta pruning m = do

  (mlink, mty) <- readMeta m >>= \case
    Unsolved mlink a -> pure (mlink, a)
    _                -> impossible

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
pruneVFlex :: PartialRenaming -> MetaVar -> Spine -> IO (Tm, MetaVar, VTy)
pruneVFlex pren m sp = do

  (sp :: [(Maybe Tm, Icit)], status :: SpinePruneStatus) <- let
    go SNil          = pure ([], OKRenaming)
    go (SApp sp t i) = do
      (sp, status) <- go sp
      case force t of
        VVar x -> case (IM.lookup (coerce x) (ren pren), status) of
                    (Just x , _            ) -> pure ((Just (Var (lvl2Ix (dom pren) x)), i):sp, status)
                    (Nothing, OKNonRenaming) -> throwIO UnifyError
                    (Nothing, _            ) -> pure ((Nothing, i):sp, NeedsPruning)
        t      -> case status of
                    NeedsPruning -> throwIO UnifyError
                    _            -> do {t <- rename pren t; pure ((Just t, i):sp, OKNonRenaming)}
    go _ = throwIO UnifyError
    in go sp

  (m', mty') <- case status of
    OKRenaming    -> readMeta m >>= \case Unsolved _ a -> pure (m, a); _ -> impossible
    OKNonRenaming -> readMeta m >>= \case Unsolved _ a -> pure (m, a); _ -> impossible
    NeedsPruning  -> pruneMeta (map (\(mt, i) -> i <$ mt) sp) m

  let t = foldr (\(mu, i) t -> maybe t (\u -> App t u i) mu) (Meta m') sp
  pure (t, m', mty')

renameSp :: PartialRenaming -> Tm -> Spine -> IO Tm
renameSp pren t = \case
  SNil              -> pure t
  SApp sp u i       -> App <$> renameSp pren t sp <*> rename pren u <*> pure i
  SProj1 sp         -> Proj1 <$> renameSp pren t sp
  SProj2 sp         -> Proj2 <$> renameSp pren t sp
  SProjField sp x n -> ProjField <$> renameSp pren t sp <*> pure x <*> pure n

rename :: PartialRenaming -> Val -> IO Tm
rename pren t = case force t of

  VFlex m' sp -> do

    case occ pren of

      -- no occurs check
      Nothing -> do
        (t, _, _) <- pruneVFlex pren m' sp
        pure t

      -- occurs check
      Just m  -> case compareMetas m m' of

        EQ ->
          throwIO UnifyError -- occurs check

        LT -> do            -- m' is out of scope, we have to strengthen it
          (t, m', mty') <- pruneVFlex pren m' sp
          mty' <- rename (PRen (Just m) 0 0 mempty) mty'
          strengthenMeta m m' (eval [] mty')
          pure t

        GT -> do            -- m' is in scope
          (t, _, _) <- pruneVFlex pren m' sp
          pure t

  VRigid (Lvl x) sp -> case IM.lookup x (ren pren) of
    Nothing -> throwIO UnifyError  -- scope error ("escaping variable" error)
    Just x' -> renameSp pren (Var $ lvl2Ix (dom pren) x') sp

  VLam x i t  -> Lam x i <$> rename (lift pren) (t $$ VVar (cod pren))
  VPi x i a b -> Pi x i <$> rename pren a <*> rename (lift pren) (b $$ VVar (cod pren))
  VSg x a b   -> Sg x <$> rename pren a <*> rename (lift pren) (b $$ VVar (cod pren))
  VPair t u   -> Pair <$> rename pren t <*> rename pren u
  VU          -> pure U

-- | Wrap a term in Lvl number of metas. We get the domain info from the
--   VTy argument.
lams :: Lvl -> VTy -> Tm -> Tm
lams l a t = go a (0 :: Lvl) where
  go a l' | l' == l = t
  go a l' = case force a of
    VPi "_" i a b -> Lam ("x"++show l') i $ go (b $$ VVar l') (l' + 1)
    VPi x i a b   -> Lam x i $ go (b $$ VVar l') (l' + 1)
    _             -> impossible

-- | Solve (Γ ⊢ m spine =? rhs)
solve :: Lvl -> MetaVar -> Spine -> Val -> IO ()
solve gamma m sp rhs = try (invert gamma sp) >>= \case
  Left NeedExpansion -> etaExpandMeta m >> unify gamma (VFlex m sp) rhs
  Left e             -> throwIO e
  Right pren         -> solveWithPRen m pren rhs

-- | Solve m given the result of inversion on a spine.
solveWithPRen :: MetaVar -> (PartialRenaming, Maybe Pruning) -> Val -> IO ()
solveWithPRen m (pren, pruneNonlinear) rhs = do

  (mlink, mty) <- readMeta m >>= \case
    Unsolved mlink a -> pure (mlink, a)
    _                -> impossible

  -- if the spine was non-linear, we check that the non-linear arguments
  -- can be pruned from the meta type (i.e. that the pruned solution will
  -- be well-typed)
  case pruneNonlinear of
    Nothing -> pure ()
    Just pr -> () <$ pruneTy (revPruning pr) mty

  rhs <- rename (pren {occ = Just m}) rhs
  let solution = eval [] $ lams (dom pren) mty rhs
  modifyIORef' mcxt $ IM.insert (coerce m) (Solved mlink solution mty)

unifyProjField :: Lvl -> Spine -> (Spine, Int) -> IO ()
unifyProjField l sp (!sp', !n) = case (sp, sp', n) of
  (sp,        sp', 0) -> unifySp l sp sp'
  (SProj2 sp, sp', n) -> unifyProjField l sp (sp', n - 1)
  _                   -> throwIO UnifyError

unifySp :: Lvl -> Spine -> Spine -> IO ()
unifySp l sp sp' = case (sp, sp') of
  (SNil              , SNil               ) -> pure ()
  (SApp sp t _       , SApp sp' t' _      ) -> unifySp l sp sp' >> unify l t t'
  (SProj1 sp         , SProj1 sp'         ) -> unifySp l sp sp'
  (SProj2 sp         , SProj2 sp'         ) -> unifySp l sp sp'
  (SProjField sp _ n , SProjField sp' _ n') -> unifySp l sp sp' >> unless (n == n') (throwIO UnifyError)
  (SProjField sp _ n , SProj1 sp'         ) -> unifyProjField l sp' (sp, n)
  (SProj1 sp         , SProjField sp' _ n') -> unifyProjField l sp (sp', n')
  _                                         -> throwIO UnifyError

-- | Solve (Γ ⊢ m spine =? m' spine').
flexFlex :: Lvl -> MetaVar -> Spine -> MetaVar -> Spine -> IO ()
flexFlex gamma m sp m' sp'

  -- usually, a longer spine indicates that the meta is in an inner scope. If we solve
  -- inner metas with outer metas, that means that we have to do less pruning.
  | spineLen sp < spineLen sp' = flexFlex gamma m' sp' m sp

flexFlex gamma m sp m' sp' =

  -- It may be that only one of the two spines is invertible
  try @UnifyError (invert gamma sp) >>= \case
    Left _      -> do {pren <- invert gamma sp'; solveWithPRen m' pren (VFlex m sp)}
    Right pren  -> solveWithPRen m pren (VFlex m' sp')

-- | Try to solve the problem (Γ ⊢ m spine =? m spine') by intersection.
--   If spine and spine' are both renamings, but different, then
--   we prune all arguments from m which differ in spine and spine'.
--
--   If some of spine/spine' are not renamings, we fall back to simple unification.
intersect :: Lvl -> MetaVar -> Spine -> Spine -> IO ()
intersect l m sp sp' = do

  let go SNil SNil = Just []
      go (SApp sp t i) (SApp sp' t' i') =
        case (force t, force t') of
          (VVar x, VVar x') -> ((i <$ guard (x == x')):) <$> go sp sp'
          _                 -> Nothing
      go _ _ = Nothing

  case go sp sp' of
    Nothing -> unifySp l sp sp'
    Just pr -> () <$ pruneMeta pr m

unify :: Lvl -> Val -> Val -> IO ()
unify l t u = case (force t, force u) of
  (VU         , VU             ) -> pure ()
  (VPi x i a b, VPi x' i' a' b') | i == i' -> unify l a a' >> unify (l + 1) (b $$ VVar l) (b' $$ VVar l)
  (VSg x a b  , VSg x' a' b'   )           -> unify l a a' >> unify (l + 1) (b $$ VVar l) (b' $$ VVar l)
  (VRigid x sp, VRigid x' sp'  ) | x == x' -> unifySp l sp sp'
  (VFlex m sp , VFlex m' sp'   ) | m == m' -> intersect l m sp sp'
  (VFlex m sp , VFlex m' sp'   )           -> flexFlex l m sp m' sp'

  (VLam _ _ t , VLam _ _ t'    ) -> unify (l + 1) (t $$ VVar l) (t' $$ VVar l)
  (t          , VLam _ i t'    ) -> unify (l + 1) (vApp t (VVar l) i) (t' $$ VVar l)
  (VLam _ i t , t'             ) -> unify (l + 1) (t $$ VVar l) (vApp t' (VVar l) i)

  (VPair t u  , VPair t' u'    ) -> unify l t t' >> unify l u u'
  (VPair t u  , t'             ) -> unify l t (vProj1 t') >> unify l u (vProj2 t')
  (t          , VPair t' u'    ) -> unify l (vProj1 t) t' >> unify l (vProj2 t) u'

  (VFlex m sp , t'             ) -> solve l m sp t'
  (t          , VFlex m' sp'   ) -> solve l m' sp' t
  _                              -> throwIO UnifyError  -- rigid mismatch error
