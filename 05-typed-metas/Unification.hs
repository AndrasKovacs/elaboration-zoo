
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
    dom :: Lvl             -- size of Γ
  , cod :: Lvl             -- size of Δ
  , ren :: IM.IntMap Lvl}  -- mapping from Δ vars to Γ vars

-- Lifting a partial renaming over an extra bound variable.
-- Given (σ : PRen Γ Δ), (lift σ : PRen (Γ, x : A[σ]) (Δ, x : A))
lift :: PartialRenaming -> PartialRenaming
lift (PRen dom cod ren) =
  PRen (dom + 1) (cod + 1) (IM.insert (unLvl cod) dom ren)

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
  pure $ PRen dom gamma ren

-- perform the partial renaming on rhs, while also checking for "m" occurrences.
rename :: Dbg => MetaVar -> PartialRenaming -> Val -> IO Tm
rename m pren v = go pren v where

  goSp :: Dbg => PartialRenaming -> Tm -> Spine -> IO Tm
  goSp pren t []             = pure t
  goSp pren t (sp :> (u, i)) = App <$> goSp pren t sp <*> go pren u <*> pure i

  go :: Dbg => PartialRenaming -> Val -> IO Tm
  go pren t = case force t of

    VFlex m' sp -> case compareMetas m m' of

      Same ->
        throwIO UnifyError -- occurs check

      Less ma' -> do
        a' <- rename m (PRen 0 0 mempty) ma'
        strengthenMeta m m' (eval [] a')
        goSp pren (Meta m') sp

      Greater ->
        goSp pren (Meta m') sp

    VRigid (Lvl x) sp -> case IM.lookup x (ren pren) of
      Nothing -> throwIO UnifyError  -- scope error ("escaping variable" error)
      Just x' -> goSp pren (Var $ lvl2Ix (dom pren) x') sp

    VLam x i t  -> Lam x i <$> go (lift pren) (t $$ VVar (cod pren))
    VPi x i a b -> Pi x i <$> go pren a <*> go (lift pren) (b $$ VVar (cod pren))
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
  rhs  <- rename m pren rhs
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
  (VLam _ _ t , VLam _ _ t'    ) -> unify (l + 1) (t $$ VVar l) (t' $$ VVar l)
  (t          , VLam _ i t'    ) -> unify (l + 1) (vApp t (VVar l) i) (t' $$ VVar l)
  (VLam _ i t , t'             ) -> unify (l + 1) (t $$ VVar l) (vApp t' (VVar l) i)
  (VU         , VU             ) -> pure ()
  (VPi x i a b, VPi x' i' a' b') | i == i' -> unify l a a' >> unify (l + 1) (b $$ VVar l) (b' $$ VVar l)
  (VRigid x sp, VRigid x' sp'  ) | x == x' -> unifySp l sp sp'
  (VFlex m sp , VFlex m' sp'   ) | m == m' -> unifySp l sp sp'

  (VFlex m sp , t'           ) -> solve l m sp t'
  (t          , VFlex m' sp' ) -> solve l m' sp' t
  _                            -> throwIO UnifyError  -- rigid mismatch error
