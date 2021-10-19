
module Elaboration (check, infer, checkEverything) where

import Control.Exception
import Control.Monad
import Data.IORef

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Map.Strict as M

import Common
import Cxt
import Errors
import Evaluation
import Metacontext
import Pretty
import Syntax
import Value

import qualified Presyntax as P

-- Postponed checking
--------------------------------------------------------------------------------

-- | Unify the result of a postponed checking with its placeholder metavariable.
unifyPlaceholder :: Dbg => Cxt -> Tm -> MetaVar -> IO ()
unifyPlaceholder cxt t m = case lookupMeta m of

  -- If the placeholder meta is unsolved and blocks nothing, solving it cannot fail.
  Unsolved bs a | IS.null bs -> do
    debug ["solve unconstrained placeholder", show m, showTm0 (closeTm (path cxt) t)]

    -- we can simply close the checked term, to get the solution
    let solution = closeTm (path cxt) t
    writeMeta m (Solved (eval [] solution) a)

  Unsolved _ _ -> do
    debug ["unify unsolved placeholder", showTm cxt t, show m]

    unifyCatch cxt
      (eval (env cxt) t)
      (vAppPruning (env cxt) (VMeta m) (pruning cxt))
      Placeholder

  Solved v _ -> do
    debug ["unify solved placeholder", showTm cxt t, show m, showVal cxt v]

    unifyCatch cxt
      (eval (env cxt) t)
      (vAppPruning (env cxt) v (pruning cxt))
      Placeholder

-- | Try to perform a delayed checking.
retryCheck :: Dbg => CheckVar -> IO ()
retryCheck c = case lookupCheck c of
  Unchecked cxt t a m -> case force a of
    -- still blocked by another meta
    VFlex m' _ -> do
      addBlocking c m'

    -- checking unblocked
    a -> do
      t <- check cxt t a
      unifyPlaceholder cxt t m
      writeCheck c $ Checked t
  _ ->
    pure ()

-- | Unblock and perform all remaining checking problems, assuming each time
--   that no implicit insertion should occur.
checkEverything :: Dbg => IO ()
checkEverything = go 0 where
  go :: CheckVar -> IO ()
  go c = do
    c' <- readIORef nextCheckVar
    when (c < c') $ do
      case lookupCheck c of
        Unchecked cxt t a m -> do

          debug ["checkEverything", show c, show c']

          (t, tty) <- insert cxt $ infer cxt t
          writeCheck c (Checked t)
          unifyCatch cxt a tty ExpectedInferred
          unifyPlaceholder cxt t m
        _ ->
          pure ()
      go (c + 1)

-- Unification
--------------------------------------------------------------------------------

-- | A partial renaming from Γ to Δ.
data PartialRenaming = PRen {
    occ :: Maybe MetaVar   -- ^ Optional occurs check.
  , dom :: Lvl             -- ^ Size of Γ.
  , cod :: Lvl             -- ^ Size of Δ.
  , ren :: IM.IntMap Lvl}  -- ^ Mapping from Δ vars to Γ vars.

-- | @lift : (σ : PRen Γ Δ) → PRen (Γ, x : A[σ]) (Δ, x : A)@
lift :: PartialRenaming -> PartialRenaming
lift (PRen occ dom cod ren) = PRen occ (dom + 1) (cod + 1) (IM.insert (unLvl cod) dom ren)

-- | @skip : PRen Γ Δ → PRen Γ (Δ, x : A)@
skip :: PartialRenaming -> PartialRenaming
skip (PRen occ dom cod ren) = PRen occ dom (cod + 1) ren

-- | @invert : (Γ : Cxt) → (spine : Sub Δ Γ) → PRen Γ Δ@
--   Optionally returns a pruning of nonlinear spine entries, if there's any.
invert :: Dbg => Lvl -> Spine -> IO (PartialRenaming, Maybe Pruning)
invert gamma sp = do

  let go :: Spine -> IO (Lvl, IM.IntMap Lvl, Pruning, Bool)
      go []             = pure (0, mempty, [], True)
      go (sp :> (t, i)) = do
        (dom, ren, pr, isLinear) <- go sp
        case force t of
          VVar (Lvl x) -> case IM.member x ren of
            True  -> pure (dom + 1, IM.delete x ren    , Nothing : pr, False   )
            False -> pure (dom + 1, IM.insert x dom ren, Just i  : pr, isLinear)
          _ -> throwIO UnifyException

  (dom, ren, pr, isLinear) <- go sp
  pure (PRen Nothing dom gamma ren, pr <$ guard isLinear)


-- | Remove some arguments from a closed iterated Pi type.
pruneTy :: Dbg => RevPruning -> VTy -> IO Ty
pruneTy (RevPruning pr) a = go pr (PRen Nothing 0 0 mempty) a where
  go pr pren a = case (pr, force a) of
    ([]          , a          ) -> rename pren a
    (Just{}  : pr, VPi x i a b) -> Pi x i <$> rename pren a
                                          <*> go pr (lift pren) (b $$ VVar (cod pren))
    (Nothing : pr, VPi x i a b) -> go pr (skip pren) (b $$ VVar (cod pren))
    _                           -> impossible

-- | Prune arguments from a meta, return new meta + pruned type.
pruneMeta :: Dbg => Pruning -> MetaVar -> IO MetaVar
pruneMeta pruning m = do

  (bs, mty) <- readMeta m >>= \case
    Unsolved bs a -> pure (bs, a)
    _             -> impossible

  prunedty <- eval [] <$> pruneTy (revPruning pruning) mty
  m' <- newRawMeta bs prunedty
  let solution = eval [] $ lams (Lvl $ length pruning) mty $ AppPruning (Meta m') pruning
  writeMeta m (Solved solution mty)
  pure m'

data SpinePruneStatus
  = OKRenaming    -- ^ Valid spine which is a renaming
  | OKNonRenaming -- ^ Valid spine but not a renaming (has a non-var entry)
  | NeedsPruning  -- ^ A spine which is a renaming and has out-of-scope var entries

-- | Prune illegal var occurrences from a meta + spine.
--   Returns: renamed + pruned term.
pruneVFlex :: Dbg => PartialRenaming -> MetaVar -> Spine -> IO Tm
pruneVFlex pren m sp = do

  (sp :: [(Maybe Tm, Icit)], status :: SpinePruneStatus) <- let
    go []             = pure ([], OKRenaming)
    go (sp :> (t, i)) = do
      (sp, status) <- go sp
      case force t of
        VVar x -> case (IM.lookup (coerce x) (ren pren), status) of
                    -- in-scope variable
                    (Just x , _            ) -> pure ((Just (Var (lvl2Ix (dom pren) x)), i):sp, status)
                    -- out-of-scope variable
                    (Nothing, OKNonRenaming) -> throwIO UnifyException -- we can only prune renamings
                    (Nothing, _            ) -> pure ((Nothing, i):sp, NeedsPruning) -- mark var as to-be-pruned
        t      -> case status of
                    -- we can only prune renamings
                    NeedsPruning -> throwIO UnifyException
                    -- rename spine entry as usual
                    _            -> do {t <- rename pren t; pure ((Just t, i):sp, OKNonRenaming)}
    in go sp

  m' <- case status of
    OKRenaming    -> readMeta m >>= \case Unsolved{} -> pure m; _ -> impossible
    OKNonRenaming -> readMeta m >>= \case Unsolved{} -> pure m; _ -> impossible
    NeedsPruning  -> pruneMeta (map (\(mt, i) -> i <$ mt) sp) m

  let t = foldr (\(mu, i) t -> maybe t (\u -> App t u i) mu) (Meta m') sp
  pure t

renameSp :: Dbg => PartialRenaming -> Tm -> Spine -> IO Tm
renameSp pren t = \case
  []             -> pure t
  (sp :> (u, i)) -> App <$> renameSp pren t sp <*> rename pren u <*> pure i

rename :: Dbg => PartialRenaming -> Val -> IO Tm
rename pren t = case force t of

  VFlex m' sp -> case occ pren of
    Just m | m == m' -> throwIO UnifyException -- occurs check
    _                -> pruneVFlex pren m' sp

  VRigid (Lvl x) sp -> case IM.lookup x (ren pren) of
    Nothing -> throwIO UnifyException  -- scope error ("escaping variable" error)
    Just x' -> renameSp pren (Var $ lvl2Ix (dom pren) x') sp

  VLam x i t  -> Lam x i <$> rename (lift pren) (t $$ VVar (cod pren))
  VPi x i a b -> Pi x i <$> rename pren a <*> rename (lift pren) (b $$ VVar (cod pren))
  VU          -> pure U

-- | Wrap a term in Lvl number of lambdas. We get the domain info from the
--   VTy argument.
lams :: Dbg => Lvl -> VTy -> Tm -> Tm
lams l a t = go a (0 :: Lvl) where
  go a l' | l' == l = t
  go a l' = case force a of
    VPi "_" i a b -> Lam ("x"++show l') i $ go (b $$ VVar l') (l' + 1)
    VPi x i a b   -> Lam x i $ go (b $$ VVar l') (l' + 1)
    _             -> impossible

-- | Solve (Γ ⊢ m spine =? rhs)
solve :: Dbg => Lvl -> MetaVar -> Spine -> Val -> IO ()
solve gamma m sp rhs = do
  pren <- invert gamma sp
  solveWithPRen gamma m pren rhs

-- | Solve m given the result of inversion on a spine.
solveWithPRen :: Dbg => Lvl -> MetaVar -> (PartialRenaming, Maybe Pruning) -> Val -> IO ()
solveWithPRen gamma m (pren, pruneNonlinear) rhs = do

  debug ["solve", show m, showTm0 (quote gamma rhs)]

  (blocked, mty) <- readMeta m >>= \case
    Unsolved blocked a -> pure (blocked, a)
    _                  -> impossible

  -- if the spine was non-linear, we check that the non-linear arguments
  -- can be pruned from the meta type (i.e. that the pruned solution will
  -- be well-typed)
  case pruneNonlinear of
    Nothing -> pure ()
    Just pr -> () <$ pruneTy (revPruning pr) mty

  rhs <- rename (pren {occ = Just m}) rhs
  let solution = eval [] $ lams (dom pren) mty rhs
  writeMeta m (Solved solution mty)

  -- retry all blocked problems
  forM_ (IS.toList blocked) (retryCheck . CheckVar)


unifySp :: Dbg => Lvl -> Spine -> Spine -> IO ()
unifySp l sp sp' = case (sp, sp') of
  ([]          , []            ) -> pure ()

  -- Note: we don't have to compare Icit-s, since we know from the recursive
  -- call that sp and sp' have the same type.
  (sp :> (t, _), sp' :> (t', _)) -> unifySp l sp sp' >> unify l t t'
  _                              -> throwIO UnifyException -- rigid mismatch error


-- | Solve (Γ ⊢ m spine =? m' spine').
flexFlex :: Dbg => Lvl -> MetaVar -> Spine -> MetaVar -> Spine -> IO ()
flexFlex gamma m sp m' sp' = let

  -- It may be that only one of the two spines is invertible
  go :: Dbg => MetaVar -> Spine -> MetaVar -> Spine -> IO ()
  go m sp m' sp' = try (invert gamma sp) >>= \case
    Left UnifyException -> solve gamma m' sp' (VFlex m sp)
    Right pren          -> solveWithPRen gamma m pren (VFlex m' sp')

  -- usually, a longer spine indicates that the meta is in an inner scope. If we solve
  -- inner metas with outer metas, that means that we have to do less pruning.
  in if length sp < length sp' then go m' sp' m sp
                               else go m sp m' sp'

-- | Try to solve the problem (Γ ⊢ m spine =? m spine') by intersection.
--   If spine and spine' are both renamings, but different, then
--   we prune all arguments from m which differ in spine and spine'.
--
--   If some of spine/spine' are not renamings, we fall back to simple unification.
intersect :: Dbg => Lvl -> MetaVar -> Spine -> Spine -> IO ()
intersect l m sp sp' = do

  let go [] [] = Just []
      go (sp :> (t, i)) (sp' :> (t', _)) =
        case (force t, force t') of
          (VVar x, VVar x') -> ((i <$ guard (x == x')):) <$> go sp sp'
          _                 -> Nothing
      go _ _ = impossible

  case go sp sp' of
    Nothing -> unifySp l sp sp'
    Just pr | any (==Nothing) pr -> () <$ pruneMeta pr m  -- at least 1 pruned entry
            | otherwise          -> pure ()


unify :: Dbg => Lvl -> Val -> Val -> IO ()
unify l t u = do
  debug ["unify", showTm0 (quote l t), showTm0 (quote l u)]
  case (force t, force u) of
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
    _                              -> throwIO UnifyException  -- rigid mismatch error


-- Elaboration
--------------------------------------------------------------------------------

closeVTy :: Cxt -> VTy -> VTy
closeVTy cxt a = eval [] $ closeTy (path cxt) (quote (lvl cxt) a)

freshMeta :: Dbg => Cxt -> VTy -> IO Tm
freshMeta cxt a = do
  m <- newRawMeta mempty (closeVTy cxt a)
  debug ["freshMeta", show m, showVal cxt a]
  pure $ AppPruning (Meta m) (pruning cxt)

unifyCatch :: Dbg => Cxt -> Val -> Val -> CantUnify -> IO ()
unifyCatch cxt t t' cant =
  unify (lvl cxt) t t'
  `catch` \UnifyException ->
     throwIO $ Error cxt $ CantUnify (quote (lvl cxt) t) (quote (lvl cxt) t') cant

-- | Insert fresh implicit applications.
insert' :: Dbg => Cxt -> IO (Tm, VTy) -> IO (Tm, VTy)
insert' cxt act = go =<< act where
  go (t, va) = case force va of
    VPi x Impl a b -> do
      m <- freshMeta cxt a
      let mv = eval (env cxt) m
      go (App t m Impl, b $$ mv)
    va -> pure (t, va)

-- | Insert fresh implicit applications to a term which is not
--   an implicit lambda (i.e. neutral).
insert :: Dbg => Cxt -> IO (Tm, VTy) -> IO (Tm, VTy)
insert cxt act = act >>= \case
  (t@(Lam _ Impl _), va) -> pure (t, va)
  (t               , va) -> insert' cxt (pure (t, va))

-- | Insert fresh implicit applications until we hit a Pi with
--   a particular binder name.
insertUntilName :: Dbg => Cxt -> Name -> IO (Tm, VTy) -> IO (Tm, VTy)
insertUntilName cxt name act = go =<< act where
  go (t, va) = case force va of
    va@(VPi x Impl a b) -> do
      if x == name then
        pure (t, va)
      else do
        m <- freshMeta cxt a
        let mv = eval (env cxt) m
        go (App t m Impl, b $$ mv)
    _ ->
      throwIO $ Error cxt $ NoNamedImplicitArg name

check :: Dbg => Cxt -> P.Tm -> VTy -> IO Tm
check cxt (P.SrcPos pos t) a =
  -- we handle the SrcPos case here, because we do not want to
  -- perform debug printing at position annotations.
  check (cxt {pos = pos}) t a
check cxt t a = do

  debug ["check", show (P.stripPos t), showVal cxt a]

  case (t, force a) of
    (P.SrcPos pos t, a) -> impossible

    -- If the icitness of the lambda matches the Pi type, check as usual
    (P.Lam x i ma t, VPi x' i' a' b') | either (\x -> x == x' && i' == Impl) (==i') i -> do

      case ma of
        Nothing -> pure ()
        Just a  -> do a <- check cxt a VU
                      unifyCatch cxt (eval (env cxt) a) a' LamBinderType

      Lam x i' <$> check (bind cxt x a') t (b' $$ VVar (lvl cxt))

    -- If we're checking a variable with unknown type, with an implicit function,
    -- we immediately unify types. This is a modest but useful approximation of
    -- polymorphic argument inference.
    (P.Var x, topA@(VPi _ Impl _ _))
      | Just (x, force -> a@(VFlex _ _)) <- M.lookup x (srcNames cxt) -> do
      unify (lvl cxt) a topA
      pure (Var (lvl2Ix (lvl cxt) x))

    -- Otherwise if Pi is implicit, insert a new implicit lambda
    (t, VPi x Impl a b) -> do
      Lam x Impl <$> check (newBinder cxt x a) t (b $$ VVar (lvl cxt))

    -- If the checking type is unknown, we postpone checking.
    (t, topA@(VFlex m sp)) -> do
      placeholder <- newRawMeta mempty (closeVTy cxt topA)
      c <- newCheck cxt t topA placeholder
      addBlocking c m

      debug ["postpone", show c, show (P.stripPos t), showVal cxt topA, show placeholder]

      pure $ PostponedCheck c

    (P.Let x a t u, a') -> do
      a <- check cxt a VU
      let ~va = eval (env cxt) a
      t <- check cxt t va
      let ~vt = eval (env cxt) t
      u <- check (define cxt x t vt a va) u a'
      pure (Let x a t u)

    (P.Hole, a) ->
      freshMeta cxt a

    (t, expected) -> do
      (t, inferred) <- insert cxt $ infer cxt t
      unifyCatch cxt expected inferred ExpectedInferred
      pure t

infer :: Dbg => Cxt -> P.Tm -> IO (Tm, VTy)
infer cxt (P.SrcPos pos t) =
  -- we handle the SrcPos case here, because we do not want to
  -- perform debug printing at position annotations.
  infer (cxt {pos = pos}) t

infer cxt t = do

  debug ["infer", show (P.stripPos t)]

  res <- case t of
    P.SrcPos pos t -> impossible

    P.Var x -> do
      case M.lookup x (srcNames cxt) of
        Just (x', a) -> pure (Var (lvl2Ix (lvl cxt) x'), a)
        Nothing      -> throwIO $ Error cxt $ NameNotInScope x

    P.Lam x (Right i) ma t -> do
      a  <- eval (env cxt) <$> case ma of
        Nothing -> freshMeta cxt VU
        Just a  -> check cxt a VU

      let cxt' = bind cxt x a
      (t, b) <- insert cxt' $ infer cxt' t
      pure (Lam x i t, VPi x i a $ valToClosure cxt b)

    P.Lam x Left{} ma t ->
      throwIO $ Error cxt $ InferNamedLam

    P.App t u i -> do

      -- choose implicit insertion
      (i, t, tty) <- case i of
        Left name -> do
          (t, tty) <- insertUntilName cxt name $ infer cxt t
          pure (Impl, t, tty)
        Right Impl -> do
          (t, tty) <- infer cxt t
          pure (Impl, t, tty)
        Right Expl -> do
          (t, tty) <- insert' cxt $ infer cxt t
          pure (Expl, t, tty)

      -- ensure that tty is Pi
      (a, b) <- case force tty of
        VPi x i' a b -> do
          unless (i == i') $
            throwIO $ Error cxt $ IcitMismatch i i'
          pure (a, b)
        tty -> do
          a <- eval (env cxt) <$> freshMeta cxt VU
          b <- Closure (env cxt) <$> freshMeta (bind cxt "x" a) VU
          unifyCatch cxt (VPi "x" i a b) tty ExpectedInferred
          pure (a, b)

      u <- check cxt u a
      pure (App t u i, b $$ eval (env cxt) u)

    P.U ->
      pure (U, VU)

    P.Pi x i a b -> do
      a <- check cxt a VU
      b <- check (bind cxt x (eval (env cxt) a)) b VU
      pure (Pi x i a b, VU)

    P.Let x a t u -> do
      a <- check cxt a VU
      let ~va = eval (env cxt) a
      t <- check cxt t va
      let ~vt = eval (env cxt) t
      (u, b) <- infer (define cxt x t vt a va) u
      pure (Let x a t u, b)

    P.Hole -> do
      a <- eval (env cxt) <$> freshMeta cxt VU
      t <- freshMeta cxt a
      pure (t, a)

  debug ["inferred", showTm cxt (fst res), showVal cxt (snd res)]
  pure res
