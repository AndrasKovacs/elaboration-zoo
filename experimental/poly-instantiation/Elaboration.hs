{-# options_ghc -Wno-type-defaults #-}

module Elaboration where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Foldable
import Lens.Micro.Platform

import qualified Data.IntMap.Strict as M
import qualified Data.Set           as S

import Types
import Evaluation

import Debug.Trace

debug :: (Show a , Applicative f) => a -> f ()
debug = traceShowM
-- debug x = pure ()

debugmcxt = do
  ms <- M.assocs <$> use mcxt
  debug [(x, case e of Solved{} -> True; _ -> False) | (x, e) <- ms]

-- debugmcxt = pure ()



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
    Rec a        -> go ns a
    TEmpty       -> pure ()
    TCons x a as -> go ns a >> go (x:ns) as
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
  lhsn <- quoteM (VNe (HMeta m) sp)
  rhsn <- quoteM rhs
  debug ("solveMeta", lhsn, rhsn)

  sp <- checkSp sp
  let vars = map fst sp
  rhs <- quoteM rhs
  checkSolution m vars rhs

  let wrap :: Tm -> (Name, Maybe Tm) -> Tm
      wrap t (x, Nothing) = Lam x Expl t
      wrap t (x, Just a ) = LamTel x a t

  rhs <- local (vals .~ []) $ evalM $ foldl' wrap rhs sp
  mcxt %= M.insert m (Solved rhs)

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

newMetaSpine :: (HasVals cxt Vals, HasInfo cxt Info) => M cxt [(Name, Maybe Tm)]
newMetaSpine = do
  info <- ordNubBy fst <$> view info
  vals <- ordNubBy fst <$> view vals
  mcxt <- use mcxt

  let go :: Info -> Vals -> [(Name, Maybe Tm)]
      go [] [] = []
      go ((x, i):is) (_:vs) = case i of
        Bound      -> (x, Nothing) : go is vs
        BoundTel a -> (x, Just (quote mcxt vs a)) : go is vs
        Defined    -> go is vs
      go _ _ = error "impossible"

  pure $ go info vals

-- | Create fresh meta, return the meta applied to all bound variables in scope.
newMeta :: (HasVals cxt Vals, HasInfo cxt Info) => M cxt Tm
newMeta = do
  debugmcxt
  sp <- newMetaSpine
  m  <- newMetaEntry (Unsolved mempty)

  let go :: (Name, Maybe Tm) -> Tm -> Tm
      go (x, Nothing) t = App t (Var x) Expl
      go (x, Just a)  t = AppTel a t (Var x)

  debug ("newmeta", foldr go (Meta m) sp)

  debugmcxt
  pure $ foldr go (Meta m) sp


unify :: Val -> Val -> UnifyM ()
unify = go where

  -- todo: more sophisticated unif here
  -- we could force spines even during unifying them,
  -- but here we only force it once in the beginning.
  goSp :: Head -> Head -> Spine -> Spine -> UnifyM ()
  goSp h h' s s' = do
    -- s <- forceSpM s
    -- s' <- forceSpM s'
    goSp' s s'
    where
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
  go topT topU = do
    forcedt <- forceM topT
    forcedu <- forceM topU
    nt <- quoteM forcedt
    nu <- quoteM forcedu
    debug ("unify", nt, nu)

    (freshTel :: Name -> Val -> (Val, UnifyM () -> UnifyM ())) <- do
      vs <- view vals
      pure $ \x a -> (VVar (fresh vs x), local (telBindU x a))

    (fresh :: Name -> (Val, UnifyM () -> UnifyM ())) <- do
      vs <- view vals
      pure $ \x -> (VVar (fresh vs x), local (bindU x))

    case (forcedt, forcedu) of
      (VLam (fresh -> (x, dive)) i t, VLam _ i' t') | i == i'-> do
        dive $ go (t x) (t' x)

      (VLam (fresh -> (x, dive)) i t, u) -> dive $ go (t x) (vApp u x i)
      (u, VLam (fresh -> (x, dive)) i t) -> dive $ go (vApp u x i) (t x)

      (VPi (fresh -> (x, dive)) i a b, VPi _ i' a' b') -> do
        go a a'
        dive $ go (b x) (b' x)

      (VU, VU) -> pure ()

      (VTel, VTel) -> pure ()

      (VRec a, VRec a') -> go a a'
      (VTEmpty, VTEmpty) -> pure ()
      (VTCons (fresh -> (x, dive)) a as, VTCons _ a' as') -> do
        go a a'
        dive $ go (as x) (as' x)

      (VTempty, VTempty) -> pure ()
      (VTcons t u, VTcons t' u') -> go t t' >> go u u'

      (VPiTel x a b, VPiTel _ a' b') -> do
        let (x', dive) = freshTel x a
        go a a'
        dive $ go (b x') (b' x')

      (VLamTel x a b, VLamTel _ a' b') -> do
        let (x', dive) = freshTel x a
        go a a'
        dive $ go (b x') (b' x')

      (VNe h sp, VNe h' sp') | h == h' ->
        goSp h h' sp sp'

      (t@(VNe (HMeta m) sp), t'@(VNe (HMeta m') sp')) ->
        if spLen sp > spLen sp'
        then solveMeta m sp t'
        else solveMeta m' sp' t

      (VNe (HMeta m) sp, t) -> solveMeta m sp t
      (t, VNe (HMeta m) sp) -> solveMeta m sp t

      (VPiTel x gamma b, VPi (x1@(fresh -> (vx1, dive))) Impl a' b') -> do
        p <- view pos
        gamma' <- local (const (UnifyCxt [] [] p)) $ freshMetaUnder x1 a'
        go gamma (VTCons x1 a' gamma')
        x2 <- freshM (x ++ "2")
        dive $ go (VPiTel x2 (gamma' vx1) (\ ~x2 -> b (VTcons vx1 x2))) (b' vx1)

      (VPiTel x a b, t) -> do
        go a VTEmpty
        go (b VTempty) t

      (VPi (x1@(fresh -> (vx1, dive))) Impl a' b', VPiTel x gamma b) -> do
        p <- view pos
        gamma' <- local (const (UnifyCxt [] [] p)) $ freshMetaUnder x1 a'
        go gamma (VTCons x1 a' gamma')
        x2 <- freshM (x ++ "2")
        dive $ go (b' vx1) (VPiTel x2 (gamma' vx1) (\ ~x2 -> b (VTcons vx1 x2)))

      (t, VPiTel x a b) -> do
        go a VTEmpty
        go (b VTempty) t

      (t, t') -> do
        t  <- quoteM t
        t' <- quoteM t'
        report $ UnifyError t t'

-- Elaboration
--------------------------------------------------------------------------------

st0 :: St
st0 = St 0 mempty

pos0 :: SourcePos
pos0 = initialPos "(stdin)"

elabCxt0 :: ElabCxt
elabCxt0 = ElabCxt [] [] [] pos0

class Context cxt where
  bind    :: Name -> VTy -> cxt -> cxt
  telBind :: Name -> VTy -> cxt -> cxt
  define  :: Name -> Val -> VTy -> cxt -> cxt

instance Context ElabCxt where
  bind x ~a (ElabCxt vs ts is p) =
    ElabCxt ((x, Nothing):vs) ((x, a):ts) ((x, Bound):is) p
  telBind x ~a (ElabCxt vs ts is p) =
    ElabCxt ((x, Nothing):vs) ((x, VRec a):ts) ((x, BoundTel a):is) p
  define x ~v ~a (ElabCxt vs ts is p) =
    ElabCxt ((x, Just v):vs) ((x, a):ts) ((x, Defined):is) p

instance Context UnifyCxt where
  bind x ~a = bindU x
  telBind = telBindU
  define x ~v ~a (UnifyCxt vs is p) = UnifyCxt ((x, Just v):vs) ((x, Bound):is) p

bindU x       (UnifyCxt vs is p) = UnifyCxt ((x, Nothing):vs) ((x, Bound):is) p
telBindU x ~a (UnifyCxt vs is p) = UnifyCxt ((x, Nothing):vs) ((x, BoundTel a):is) p

binding x ~a     = local (bind x a)
telBinding x ~a  = local (telBind x a)
defining x ~v ~a = local (define x v a)

embedUnifyM :: UnifyM a -> ElabM a
embedUnifyM = withReaderT (\(ElabCxt vs ts is p) -> UnifyCxt vs is p)

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
  topAn <- quoteM topA

  case (topT, topA) of
    (RSrcPos p t, _) ->
      local (pos .~ p) (check t topA)
    _ -> do
      debug ("check", topT, topAn)
      res <- case (topT, topA) of

        (RLam x ann ni t, VPi x' i' a b) | either (\x -> x == x' && i' == Impl) (==i') ni -> do
          case ann of
            Just ann -> do {ann <- evalM =<< check ann VU; embedUnifyM (unify ann a)}
            Nothing  -> pure ()
          let v = VVar (fresh x)
          local
            (\(ElabCxt vs ts is p) -> ElabCxt ((x, Just v):vs) ((x, a):ts) ((x, Bound):is) p)
            (Lam x i' <$> check t (b v))

        (t, VPi x Impl a b) -> do
          let x' = fresh x ++ "%"
          binding x' a $ Lam x' Impl <$> check t (b (VVar x'))

        (t, VNe (HMeta m) sp) -> do
          x       <- use nextMId <&> \i -> fresh $ "Γ" ++ show i
          tel     <- newMeta
          telv    <- evalM tel
          (t, va) <- telBinding x telv $ infer MIYes t
          ms      <- use mcxt
          vs      <- view vals
          ~a      <- quoteM va
          let ty  = VPiTel x telv $ \ ~u -> eval ms ((x, Just u):vs) a
          embedUnifyM (unify topA ty)
          pure $ LamTel x tel t

        (RLet x a t u, topA) -> do
          a   <- check a VU
          ~va <- evalM a
          t   <- check t va
          ~vt <- evalM t
          u   <- defining x vt va $ check u topA
          pure $ Let x a t u

        (RHole, _) ->
          newMeta

        _ -> do
          (t, va) <- infer MIYes topT
          embedUnifyM $ unify va topA
          pure t

      debug ("checked", topT)
      pure res


-- | Create a fresh meta under a given binder.
freshMetaUnder ::
  (HasInfo cxt Info, HasVals cxt Vals, Context cxt) => Name -> Val -> M cxt (Val -> VTy)
freshMetaUnder x ~va = do
  b    <- binding x va newMeta
  mcxt <- use mcxt
  vals <- view vals
  pure (\ ~u -> eval mcxt ((x, Just u):vals) b)

-- | Create a fresh domain and codomain type.
freshPi ::
  (HasVals cxt Vals, HasInfo cxt Info, Context cxt) => Name -> M cxt (VTy, Val -> VTy)
freshPi x = do
  a <- newMeta
  va <- evalM a
  b <- freshMetaUnder x va
  pure (va, b)

infer :: MetaInsertion -> Raw -> ElabM (Tm, VTy)
infer ins t = case t of
  RSrcPos p t -> local (pos .~ p) (infer ins t)
  t -> do
    debug ("infer"::String, t)
    res <- case t of
      RSrcPos{} -> error "impossible"
      RVar x -> insertMetas ins $
        (lookup x <$> view types) >>= \case
          Nothing -> report $ NameNotInScope x
          Just a  -> pure (Var x, a)

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

      RLam x _ (Right i) t -> insertMetas ins $ do
        a <- newMeta
        va <- evalM a
        (t, b) <- binding x va $ infer MIYes t
        ~nb <- binding x va $ quoteM b
        ms <- use mcxt
        vs <- view vals
        pure (Lam x i t, VPi x i va (\u -> eval ms ((x, Just u):vs) nb))

        -- (a, b) <- case ann of
        --   Just a -> do
        --     a <- evalM =<< check a VU
        --     b <- freshMetaUnder x a
        --     pure (a, b)
        --   Nothing -> do
        --     freshPi x
        -- let pi = VPi x i a b
        -- t <- check (RLam x Nothing (Right i) t) pi
        -- pure (t, pi)

      RPi x i a b -> do
        a   <- check a VU
        ~va <- evalM a
        b   <- binding x va $ check b VU
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
        (!u, vb) <- defining x vt va $ infer ins u
        pure (Let x a t u, vb)

      RStopInsertion t ->
        infer MINo t

    debug ("inferred", t)
    pure res

--------------------------------------------------------------------------------

-- | Inline all meta solutions, compute telescopes.
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
      either (\t -> Left (vAppTel ms (eval ms vs a) t (eval ms vs u)))
             (\t -> Right (AppTel (go vs u) t (go vs u)))
             (goSp vs t)
    t -> Right (go vs t)

  goBind vs x = go ((x, Nothing):vs)

  go :: Vals -> Tm -> Tm
  go vs = \case
    Var x        -> Var x
    Meta x       -> case ms M.! x of
                     Solved v    -> quote ms vs v
                     _           -> Meta x
    U            -> U
    Pi x i a b   -> Pi x i (go vs a) (goBind vs x b)
    App t u ni   -> either (\t -> quote ms vs (vApp t (eval ms vs u) ni))
                           (\t -> App t (go vs u) ni)
                           (goSp vs t)
    Lam x i t    -> Lam x i (goBind vs x t)
    Let x a t u  -> Let x (go vs a) (go vs t) (goBind vs x u)

    Tel         -> Tel
    TEmpty      -> TEmpty
    TCons x t u -> TCons x (go vs t) (goBind vs x u)
    Rec a       -> Rec (go vs a)
    Tempty      -> Tempty
    Tcons t u   -> Tcons (go vs t) (go vs u)
    Proj1 t     -> Proj1 (go vs t)
    Proj2 t     -> Proj2 (go vs t)
    PiTel x a b -> PiTel x (go vs a) (goBind vs x b)

    AppTel a t u -> either (\t -> quote ms vs (vAppTel ms (eval ms vs a) t (eval ms vs u)))
                           (\t -> AppTel (go vs a) t (go vs u))
                           (goSp vs t)
    LamTel x a b -> LamTel x (go vs a) (goBind vs x b)

zonkM :: HasVals cxt Vals => Tm -> M cxt Tm
zonkM t = zonk <$> use mcxt <*> view vals <*> pure t
