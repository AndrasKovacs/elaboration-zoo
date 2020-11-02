
module Unification (unify) where

import Control.Exception
import Data.IORef
import qualified Data.IntMap as IM

import Common
import Errors
import Evaluation
import Metacontext
import Syntax
import Value

-- Unification
--------------------------------------------------------------------------------

-- partial renaming from Γ to Δ
data PartialRenaming = PRen {
    occ :: Maybe MetaVar   -- optional occurs check
  , dom :: Lvl             -- size of Γ
  , cod :: Lvl             -- size of Δ
  , ren :: IM.IntMap Lvl}  -- mapping from Δ vars to Γ vars

-- lift : (σ : PRen Γ Δ) → PRen (Γ, x : A[σ]) (Δ, x : A)
lift :: PartialRenaming -> PartialRenaming
lift (PRen occ dom cod ren) =
  PRen occ (dom + 1) (cod + 1) (IM.insert (unLvl cod) dom ren)

-- weaken : PRen Γ Δ → PRen (Γ, A) Δ
-- weaken σ = σ ∘ (p : Sub (Γ, A) Γ)
weaken :: PartialRenaming -> PartialRenaming
weaken (PRen occ dom cod ren) = PRen occ (dom + 1) cod ren

-- invert : (Γ : Cxt) → (spine : Sub Δ Γ) → PRen Γ Δ
invert :: Dbg => Lvl -> Spine -> IO PartialRenaming
invert gamma sp = do

  let go :: Dbg => Spine -> IO (Lvl, IM.IntMap Lvl)
      go []             = pure (0, mempty)
      go (sp :> (t, _)) = do
        (dom, ren) <- go sp
        case force t of
          VVar (Lvl x) | IM.notMember x ren -> pure (dom + 1, IM.insert x dom ren)
          _                                 -> throwIO UnifyError

  (dom, ren) <- go sp
  pure $ PRen Nothing dom gamma ren


data PruneStatus = OKRenaming | OKNonRenaming | NeedsPruning

-- [x, y, z]  -- OKRenaming: valid spine which is a renaming
--            -- OKNonRenaming: valid but has something which is not a var
--            -- NeedsPruning: renaming with some illegal variables

-- (we can only do pruning on renamings!)

-- ?1 x =? (?0 [x, True, y])    -- can we prune y?

-- ?0 : (a : A)(b : Bool)(c : if b then ... else ...) → if b then ... else ...
-- (if we only have vars in spine, dependencies cannot change (based on canonical value computation))


-- | Returns: renamed + pruned term, head meta after pruning, type of the head meta after pruning.
prune :: Dbg => PartialRenaming -> MetaVar -> Spine -> IO (Tm, MetaVar, VTy)
prune pren m sp = do

  (mlink, mty) <- readMeta m >>= \case
    Unsolved mlink a -> pure (mlink, a)
    _                -> impossible

  (sp :: [(Maybe Tm, Icit)], status :: PruneStatus) <- let
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

  case status of
    OKRenaming    -> pure (foldr (\(Just u, i) t -> App t u i) (Meta m) sp, m, mty)
    OKNonRenaming -> pure (foldr (\(Just u, i) t -> App t u i) (Meta m) sp, m, mty)
    NeedsPruning  -> do

      -- mty is the un-pruned type of "m"
      -- I want to compute a type which has fewer Pi arguments
      prunedty <- let
        go :: [(Maybe Tm, Icit)] -> PartialRenaming -> VTy -> IO Ty
        go sp pren a = case (sp, force a) of
          ([]               , a          ) -> rename pren a
          ((Just _ , _) : sp, VPi x i a b) -> Pi x i <$> rename pren a
                                                     <*> go sp (lift pren) (b $$ VVar (cod pren))
          ((Nothing, _) : sp, VPi x i a b) -> go sp (weaken pren) (b $$ VVar (cod pren))
          _                                -> impossible

        in eval [] <$> go (reverse sp) (PRen Nothing 0 0 mempty) mty

      m' <- pushMeta prunedty
      let metaPruning = map (\(mt, i) -> i <$ mt) sp
      let solution = eval [] $ lams (Lvl $ length sp) mty $ AppPruning (Meta m') metaPruning

      -- solve the old meta with the new pruned meta
      modifyIORef' mcxt $ IM.insert (coerce m) (Solved mlink solution mty)
      pure (foldr (\(mu, i) t -> maybe t (\u -> App t u i) mu) (Meta m') sp, m', prunedty)


renameSp :: Dbg => PartialRenaming -> Tm -> Spine -> IO Tm
renameSp pren t = \case
  []             -> pure t
  (sp :> (u, i)) -> App <$> renameSp pren t sp <*> rename pren u <*> pure i

-- perform the partial renaming on rhs, while also checking for "m" occurrences.
rename :: Dbg => PartialRenaming -> Val -> IO Tm
rename pren t = case force t of

  -- rename some
  VFlex m' sp -> do

    case occ pren of  -- are we doing meta occurs check?
      Nothing -> do
        (t, _, _) <- prune pren m' sp
        pure t

      Just m  -> case compareMetas m m' of
        EQ ->
          throwIO UnifyError     -- occurs check

        LT -> do            -- to-be-solved meta is earlier in the context
                            -- I have to move m' before m
          (t, m', mty') <- prune pren m' sp
          mty' <- rename (PRen (Just m) 0 0 mempty) mty'
          strengthenMeta m m' (eval [] mty')
          pure t

        GT -> do            -- to-be-solved meta already has m' in scope
          (t, _, _) <- prune pren m' sp
          pure t


  VRigid (Lvl x) sp -> case IM.lookup x (ren pren) of
    Nothing -> throwIO UnifyError                             -- scope error ("escaping variable" error)
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

solve :: Dbg => Lvl -> MetaVar -> Spine -> Val -> IO ()
solve gamma m sp rhs = do
  (mlink, mty) <- readMeta m >>= \case
    Unsolved mlink a -> pure (mlink, a)
    _                -> impossible
  pren <- invert gamma sp
  rhs  <- rename (pren {occ = Just m}) rhs
  let solution = eval [] $ lams (dom pren) mty rhs
  modifyIORef' mcxt $ IM.insert (coerce m) (Solved mlink solution mty)

unifySp :: Dbg => Lvl -> Spine -> Spine -> IO ()
unifySp l sp sp' = case (sp, sp') of
  ([]          , []            ) -> pure ()

  -- Note: we don't have to compare Icit-s, since we know from the recursive
  -- call that sp and sp' have the same type.
  (sp :> (t, _), sp' :> (t', _)) -> unifySp l sp sp' >> unify l t t'
  _                              -> throwIO UnifyError -- rigid mismatch error

unify :: Dbg => Lvl -> Val -> Val -> IO ()
unify l t u = case (force t, force u) of
  (VU         , VU             ) -> pure ()
  (VPi x i a b, VPi x' i' a' b') | i == i' -> unify l a a' >> unify (l + 1) (b $$ VVar l) (b' $$ VVar l)
  (VRigid x sp, VRigid x' sp'  ) | x == x' -> unifySp l sp sp'
  (VFlex m sp , VFlex m' sp'   ) | m == m' -> unifySp l sp sp'
  (VLam _ _ t , VLam _ _ t'    ) -> unify (l + 1) (t $$ VVar l) (t' $$ VVar l)
  (t          , VLam _ i t'    ) -> unify (l + 1) (vApp t (VVar l) i) (t' $$ VVar l)
  (VLam _ i t , t'             ) -> unify (l + 1) (t $$ VVar l) (vApp t' (VVar l) i)
  (VFlex m sp , t'             ) -> solve l m sp t'
  (t          , VFlex m' sp'   ) -> solve l m' sp' t
  _                              -> throwIO UnifyError  -- rigid mismatch error
