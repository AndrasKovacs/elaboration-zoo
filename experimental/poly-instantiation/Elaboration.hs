
module Elaboration where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Foldable
import Lens.Micro.Platform

import qualified Data.IntMap.Strict as M
import qualified Data.Set           as S

import Presyntax
import Types
import Evaluation


-- Unification
--------------------------------------------------------------------------------

report :: HasPos cxt SourcePos => ElabError -> M cxt a
report err = do
  pos <- view pos
  throwError (Err err pos)

-- | Expects a forced spine.
checkSp :: Spine -> UnifyM (Sub (Maybe Tm))
checkSp = \case
  SNil -> pure []
  SApp sp u i -> forceM u >>= \case
    VVar x -> ((x, Nothing):) <$> checkSp sp
    v      -> do {t <- quoteM v; report $ SpineNonVar t}
  SAppTel a sp u -> forceM u >>= \case
    VVar x -> do {a <- quoteM a; ((x, Just a):) <$> checkSp sp}
    v      -> do {t <- quoteM v; report $ SpineNonVar t}
  SProj1{} -> report SpineProjection
  SProj2{} -> report SpineProjection

-- | Expects a normal form.
checkSolution :: MId -> [Name] -> Tm -> UnifyM ()
checkSolution m vars rhs = go vars rhs where
  go ns = \case
    Var x        -> unless (elem x ns) $ report $ ScopeError m vars rhs x
    Pi x i a b   -> go ns a >> go (x:ns) b
    U            -> pure ()
    Meta m'      -> when (m == m') $ report $ OccursCheck m rhs
    App t u _    -> go ns t >> go ns u
    Lam x i t    -> go (x:ns) t
    Tel          -> pure ()
    El a         -> go ns a
    TEmpty       -> pure ()
    TCons a as   -> go ns a >> go ns as
    Tempty       -> pure ()
    Tcons t u    -> go ns t >> go ns u
    Proj1 t      -> go ns t
    Proj2 t      -> go ns t
    PiTel x a b  -> go ns a >> go (x:ns) b
    AppTel a t u -> go ns a >> go ns t >> go ns u
    LamTel x a t -> go ns a >> go (x:ns) t
    Let{}        -> error "impossible"

solveMeta :: MId -> Spine -> Val -> UnifyM ()
solveMeta m sp rhs = do
  sp <- checkSp sp
  let vars = map fst sp
  rhs <- quoteM rhs
  checkSolution m vars rhs

  let wrap :: Tm -> (Name, Maybe Tm) -> Tm
      wrap t (x, Nothing) = Lam x Expl t
      wrap t (x, Just a ) = LamTel x a t

  rhs <- local (vals .~ []) $ evalM $ foldl' wrap rhs sp
  mcxt . at m ?= Solved rhs

-- | Remove duplicate elements.
ordNubBy :: Ord b => (a -> b) -> [a] -> [a]
ordNubBy f = go S.empty where
  go s [] = []
  go s (a:as) | S.member (f a) s = go s as
              | otherwise        = a : go (S.insert (f a) s) as

newMetaEntry :: MetaEntry -> M cxt MId
newMetaEntry p = do
  St i ms <- get
  put $ St (i + 1) (M.insert i p ms)
  pure i

newMetaSpine :: ElabM [(Name, Maybe Tm)]
newMetaSpine = do
  vals  <- ordNubBy fst <$> view vals
  types <- ordNubBy fst <$> view types
  mcxt  <- use mcxt

  let go :: Vals -> Sub TyEntry -> [(Name, Maybe Tm)]
      go [] [] = []
      go (_:vs) ((x, Def{}):ts) = go vs ts
      go (_:vs) ((x, Bound a):ts) = case force mcxt a of
        VEl a -> (x, Just (quote mcxt vs a)) : go vs ts
        _     -> (x, Nothing)                : go vs ts
      go _ _ = error "impossible"

  pure $ go vals types

-- | Create fresh meta, return the meta applied to all bound variables in scope.
newMeta :: ElabM Tm
newMeta = do
  sp <- newMetaSpine
  m  <- newMetaEntry (Unsolved mempty)

  let go :: (Name, Maybe Tm) -> Tm -> Tm
      go (x, Nothing) t = App t (Var x) Expl
      go (x, Just a)  t = AppTel a t (Var x)

  pure $ foldr go (Meta m) sp

unify :: Val -> Val -> UnifyM ()
unify = go where

  -- todo: more sophisticated unif here
  -- e.g.: force AppTel on the fly, expand to App
  goSp :: Head -> Head -> Spine -> Spine -> UnifyM ()
  goSp h h' = goSp' where
    goSp' SNil SNil = pure ()
    goSp' s@(SApp sp u i) s'@(SApp sp' u' i') = do
      goSp' sp sp'
      unless (i == i') $ do
        t  <- quoteM (VNe h s)
        t' <- quoteM (VNe h' s')
        report $ UnifyError t t'
      go u u'
    goSp' (SAppTel a sp u) (SAppTel a' sp' u') = do
      go a a'
      goSp' sp sp'
      go u u'
    goSp' s s' = do
      t  <- quoteM (VNe h s)
      t' <- quoteM (VNe h' s')
      report $ UnifyError t t'

  go :: Val -> Val -> UnifyM ()
  go t u = do
    t <- forceM t
    u <- forceM u

    fresh <- do
      vs <- view vals
      pure $ \x -> (VVar (fresh vs x), local (vals %~ ((x, Left Nothing):)))

    -- freshTel <- do
    --   vs <- view vals
    --   pure $ \x -> (
    --     VVar (fresh vs x),
    --     local (vals %~ ((x, Left Nothing):)))

    case (t, u) of
      (VLam (fresh -> (x, dive)) i t, VLam _ i' t') | i == i'-> do
        dive $ go (t x) (t' x)

      (VLam (fresh -> (x, dive)) i t, u) -> dive $ go (t x) (vApp u x i)
      (u, VLam (fresh -> (x, dive)) i t) -> dive $ go (vApp u x i) (t x)

      (VPi (fresh -> (x, dive)) i a b, VPi _ i' a' b') -> do
        go a a'
        dive $ go (b x) (b' x)

      (VU, VU) -> pure ()

      (VTel, VTel) -> pure ()

      (VEl a, VEl a') -> go a a'
      (VTEmpty, VTEmpty) -> pure ()
      (VTCons a as, VTCons a' as') -> go a a' >> go as as'
      (VTempty, VTempty) -> pure ()
      (VTcons t u, VTcons t' u') -> go t t' >> go u u'

      (VPiTel (fresh -> (x, dive)) a b, VPiTel _ a' b') -> do
        undefined

      (VNe h sp, VNe h' sp') | h == h' ->
        goSp h h' sp sp'

      (t@(VNe (HMeta m) sp), t'@(VNe (HMeta m') sp')) ->
        if spLen sp > spLen sp'
        then solveMeta m sp t'
        else solveMeta m' sp' t

      (VNe (HMeta m) sp, t) -> solveMeta m sp t
      (t, VNe (HMeta m) sp) -> solveMeta m sp t

      (t, t') -> do
        t  <- quoteM t
        t' <- quoteM t'
        report $ UnifyError t t'

-- Elaboration
--------------------------------------------------------------------------------

-- | Add a bound variable to context.
bind :: Name -> VTy -> ElabM a -> ElabM a
bind x a = local $
    (vals  %~ ((x, Left Nothing):))
  . (types %~ ((x, Bound a):))

-- | Add a defined name to context.
define :: Name -> Val -> VTy -> ElabM a -> ElabM a
define x v a = local $
    (vals  %~ ((x, Right v):))
  . (types %~ ((x, Def a):))

embedUnifyM :: UnifyM a -> ElabM a
embedUnifyM = withReaderT (\(ElabCxt vs ts p) -> UnifyCxt vs p)


insertMetas :: MetaInsertion -> ElabM (Tm, VTy) -> ElabM (Tm, VTy)
insertMetas ins action = case ins of
  MINo  -> action

  MIYes -> do
    (t, va) <- action
    let go t va = forceM va >>= \case
          VPi x Impl a b -> do
            m  <- newMeta
            mv <- evalM m
            go (App t m Impl) (b mv)
          va -> pure (t, va)
    go t va

  MIUntilName x -> do
    (t, va) <- action
    let go t va = forceM va >>= \case
          va@(VPi x' Impl a b) -> do
            if x == x' then
              pure (t, va)
            else do
              m  <- newMeta
              mv <- evalM m
              go (App t m Impl) (b mv)
          _ -> report (NoNamedImplicitArg x)
    go t va

check :: Raw -> VTy -> ElabM Tm
check topT topA = do
  topA <- forceM topA
  fresh <- fresh <$> view vals

  case (topT, topA) of
    (RSrcPos p t, _) ->
      local (pos .~ p) (check t topA)

    (RLam x ann ni t, VPi x' i' a b) | either (\x -> x == x' && i' == Impl) (==i') ni -> do
      case ann of
        Just ann -> do {ann <- evalM =<< check ann VU; embedUnifyM (unify ann a)}
        Nothing  -> pure ()
      let v = VVar (fresh x)
      local
        ((vals %~ ((x, Right v):)) . (types %~ ((x, Bound a):))) $ do
          Lam x i' <$> check t (b v)

    (t, VPi x Impl a b) -> do
      let x' = fresh x ++ "%"
      bind x' a $ Lam x' Impl <$> check t (b (VVar x'))

    -- (t, VNe (HMeta m) sp) -> do
    --   x       <- use nextMId <&> \i -> fresh $ "Γ" ++ show i
    --   tel     <- newMeta
    --   telv    <- evalM tel
    --   (t, va) <- bind x (VEl telv) $ infer MIYes t
    --   ms      <- use mcxt
    --   vs      <- view vals
    --   ~a      <- quoteM va
    --   let ty  = VPiTel x telv $ \u -> eval ms ((x, Right u):vs) a
    --   embedUnifyM (unify topA ty)
    --   pure $ LamTel x tel a

    (RLet x a t u, topA) -> do
      a   <- check a VU
      ~va <- evalM a
      t   <- check t va
      ~vt <- evalM t
      u   <- define x vt va $ check u topA
      pure $ Let x a t u

    (RHole, _) ->
      newMeta

    _ -> do
      (t, va) <- infer MIYes topT
      embedUnifyM $ unify va topA
      pure t

-- | Create a fresh meta under a given binder.
freshMetaUnder :: Name -> Val -> ElabM (Val -> VTy)
freshMetaUnder x ~va = do
  b    <- bind x va newMeta
  mcxt <- use mcxt
  vals <- view vals
  pure (\u -> eval mcxt ((x, Right u):vals) b)

-- | Create a fresh domain and codomain type.
freshPi :: Name -> ElabM (VTy, Val -> VTy)
freshPi x = do
  a <- newMeta
  va <- evalM a
  b <- freshMetaUnder x va
  pure (va, b)

infer :: MetaInsertion -> Raw -> ElabM (Tm, VTy)
infer ins = \case

  RSrcPos p t -> local (pos .~ p) (infer ins t)

  RVar x -> insertMetas ins $
    (lookup x <$> view types) >>= \case
      Nothing -> report $ NameNotInScope x
      Just a  -> pure (Var x, case a of Bound a -> a; Def a -> a)

  RU -> pure (U, VU)

  RApp t u ni -> insertMetas ins $ do
    let (insertion, i) = case ni of
          Left x  -> (MIUntilName x, Impl)
          Right i -> (icit i MINo MIYes, i)
    (t, va) <- infer insertion t
    (a, b) <- forceM va >>= \case
      VPi x i' a b -> do
        unless (i == i') $
          report $ IcitMismatch i i'
        pure (a, b)
      va@(VNe (HMeta x) sp) -> do
        (a, b) <- freshPi "x"
        embedUnifyM $ unify va (VPi "x" i a b)
        pure (a, b)
      tty -> do
        tty <- quoteM tty
        report $ ExpectedFunction tty
    u <- check u a
    ~vu <- evalM u
    pure (App t u i, b vu)

  RLam _ _ Left{} _ ->
    report CannotInferNamedLam

  RLam x ann (Right i) t -> insertMetas ins $ do
    (a, b) <- case ann of
      Just a -> do
        a <- evalM =<< check a VU
        b <- freshMetaUnder x a
        pure (a, b)
      Nothing -> do
        freshPi x
    let pi = VPi x i a b
    t <- check (RLam x Nothing (Right i) t) pi
    pure (t, pi)

  RPi x i a b -> do
    a   <- check a VU
    ~va <- evalM a
    b   <- bind x va $ check b VU
    pure (Pi x i a b, VU)

  RHole -> do
    t   <- newMeta
    ~va <- evalM =<< newMeta
    pure (t, va)

  RLet x a t u -> do
    a        <- check a VU
    ~va      <- evalM a
    t        <- check t va
    ~vt      <- evalM t
    (!u, vb) <- define x vt va $ infer ins u
    pure (Let x a t u, vb)

  RStopInsertion t ->
    infer MINo t

--------------------------------------------------------------------------------

-- | Inline all meta solutions.
zonk :: MCxt -> Vals -> Tm -> Tm
zonk ms = go where

  goSp :: Vals -> Tm -> Either Val Tm
  goSp vs = \case
    Meta x -> case ms M.! x of
      Solved v -> Left v
      _        -> Right (Meta x)
    App t u ni ->
      either (\t -> Left (vApp t (eval ms vs u) ni))
             (\t -> Right (App t (go vs u) ni))
             (goSp vs t)
    AppTel a t u ->
      either (\t -> Left (vAppTel (eval ms vs a) t (eval ms vs u)))
             (\t -> Right (AppTel (go vs u) t (go vs u)))
             (goSp vs t)
    t -> Right (go vs t)

  go :: Vals -> Tm -> Tm
  go vs = \case
    Var x        -> Var x
    Meta x       -> case ms M.! x of
                     Solved v    -> quote ms vs v
                     _           -> Meta x
    U            -> U
    Pi x i a b   -> Pi x i (go vs a) (go ((x, Left Nothing):vs) b)
    App t u ni   -> either (\t -> quote ms vs (vApp t (eval ms vs u) ni))
                           (\t -> App t (go vs u) ni)
                           (goSp vs t)
    Lam x i t    -> Lam x i (go ((x, Left Nothing):vs) t)
    Let x a t u  -> Let x (go vs a) (go vs t)
                          (go ((x, Left Nothing):vs) u)

    Tel         -> Tel
    TEmpty      -> TEmpty
    TCons t u   -> TCons (go vs t) (go vs u)
    El a        -> El (go vs a)
    Tempty      -> Tempty
    Tcons t u   -> Tcons (go vs t) (go vs u)
    Proj1 t     -> Proj1 (go vs t)
    Proj2 t     -> Proj2 (go vs t)
    PiTel x a b -> PiTel x (go vs a) (go ((x, Left (Just (eval ms vs a))):vs) b)

    AppTel a t u -> either (\t -> quote ms vs (vAppTel (eval ms vs a) t (eval ms vs u)))
                           (\t -> AppTel (go vs a) t (go vs u))
                           (goSp vs t)
    LamTel x a b -> LamTel x (go vs a) (go ((x, Left (Just (eval ms vs a))):vs) b)

zonkM :: HasVals cxt Vals => Tm -> M cxt Tm
zonkM t = zonk <$> use mcxt <*> view vals <*> pure t
