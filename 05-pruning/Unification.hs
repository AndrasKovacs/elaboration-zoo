
module Unification (unify) where

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
--   Optionally returns a pruning of nonlinear spine entries, is there's any.
invert :: Lvl -> Spine -> IO (PartialRenaming, Maybe Pruning)
invert gamma sp = do

  let go :: Spine -> IO (Lvl, IM.IntMap Lvl, Pruning, Bool)
      go []             = pure (0, mempty, [], True)
      go (sp :> (t, i)) = do
        (dom, ren, pr, isLinear) <- go sp
        case force t of
          VVar (Lvl x) -> case IM.member x ren of
            True  -> pure (dom + 1, IM.delete x ren    , Nothing : pr, False   )
            False -> pure (dom + 1, IM.insert x dom ren, Just i  : pr, isLinear)
          _ -> throwIO UnifyError

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
    go []             = pure ([], OKRenaming)
    go (sp :> (t, i)) = do
      (sp, status) <- go sp
      case force t of
        VVar x -> case (IM.lookup (coerce x) (ren pren), status) of
                    (Just x , _            ) -> pure ((Just (Var (lvl2Ix (dom pren) x)), i):sp, status)
                    (Nothing, OKNonRenaming) -> throwIO UnifyError
                    (Nothing, _            ) -> pure ((Nothing, i):sp, NeedsPruning)
        t      -> case status of
                    NeedsPruning -> throwIO UnifyError
                    _            -> do {t <- rename pren t; pure ((Just t, i):sp, OKNonRenaming)}
    in go sp

  (m', mty') <- case status of
    OKRenaming    -> readMeta m >>= \case Unsolved _ a -> pure (m, a); _ -> impossible
    OKNonRenaming -> readMeta m >>= \case Unsolved _ a -> pure (m, a); _ -> impossible
    NeedsPruning  -> pruneMeta (map (\(mt, i) -> i <$ mt) sp) m

  let t = foldr (\(mu, i) t -> maybe t (\u -> App t u i) mu) (Meta m') sp
  pure (t, m', mty')


renameSp :: PartialRenaming -> Tm -> Spine -> IO Tm
renameSp pren t = \case
  []             -> pure t
  (sp :> (u, i)) -> App <$> renameSp pren t sp <*> rename pren u <*> pure i

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
solve gamma m sp rhs = do
  pren <- invert gamma sp
  solveWithPRen m pren rhs

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

unifySp :: Lvl -> Spine -> Spine -> IO ()
unifySp l sp sp' = case (sp, sp') of
  ([]          , []            ) -> pure ()

  -- Note: we don't have to compare Icit-s, since we know from the recursive
  -- call that sp and sp' have the same type.
  (sp :> (t, _), sp' :> (t', _)) -> unifySp l sp sp' >> unify l t t'
  _                              -> throwIO UnifyError -- rigid mismatch error


-- | Solve (Γ ⊢ m spine =? m' spine').
flexFlex :: Lvl -> MetaVar -> Spine -> MetaVar -> Spine -> IO ()
flexFlex gamma m sp m' sp'

  -- usually, a longer spine indicates that the meta is in an inner scope. If we solve
  -- inner metas with outer metas, that means that we have to do less pruning.
  | length sp < length sp' = flexFlex gamma m' sp' m sp

flexFlex gamma m sp m' sp' =

  -- It may be that only one of the two spines is invertible
  try (invert gamma sp) >>= \case
    Left UnifyError -> do {pren <- invert gamma sp'; solveWithPRen m' pren (VFlex m sp)}
    Right pren      -> solveWithPRen m pren (VFlex m' sp')


-- | Try to solve the problem (Γ ⊢ m spine =? m spine') by intersection.
--   If spine and spine' are both renamings, but different, then
--   we prune all arguments from m which differ in spine and spine'.
--
--   If some of spine/spine' are not renamings, we fall back to simple unification.
intersect :: Lvl -> MetaVar -> Spine -> Spine -> IO ()
intersect l m sp sp' = do

  let go [] [] = Just []
      go (sp :> (t, i)) (sp' :> (t', _)) =
        case (force t, force t') of
          (VVar x, VVar x') -> ((i <$ guard (x == x')):) <$> go sp sp'
          _                 -> Nothing
      go _ _ = impossible

  case go sp sp' of
    Nothing -> unifySp l sp sp'
    Just pr -> () <$ pruneMeta pr m


unify :: Lvl -> Val -> Val -> IO ()
unify l t u = case (force t, force u) of
  (VU         , VU             ) -> pure ()
  (VPi x i a b, VPi x' i' a' b') | i == i' -> unify l a a' >> unify (l + 1) (b $$ VVar l) (b' $$ VVar l)
  (VRigid x sp, VRigid x' sp'  ) | x == x' -> unifySp l sp sp'
  (VFlex m sp , VFlex m' sp'   ) | m == m' -> intersect l m sp sp'
  (VFlex m sp , VFlex m' sp'   )           -> flexFlex l m sp m' sp'
  (VLam _ _ t , VLam _ _ t'    ) -> unify (l + 1) (t $$ VVar l) (t' $$ VVar l)
  (t          , VLam _ i t'    ) -> unify (l + 1) (vApp t (VVar l) i) (t' $$ VVar l)
  (VLam _ i t , t'             ) -> unify (l + 1) (t $$ VVar l) (vApp t' (VVar l) i)
  (VFlex m sp , t'             ) -> solve l m sp t'
  (t          , VFlex m' sp'   ) -> solve l m' sp' t
  _                              -> throwIO UnifyError  -- rigid mismatch error
