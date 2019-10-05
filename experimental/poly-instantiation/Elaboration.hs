{-# options_ghc -Wno-type-defaults -Wno-unused-imports #-}

module Elaboration where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Foldable
import Lens.Micro.Platform
import Text.Megaparsec (initialPos)

import qualified Data.IntMap.Strict as M
import qualified Data.Set           as S

import Types
import Evaluation

--------------------------------------------------------------------------------

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
  sp <- forceSpM sp
  sp <- checkSp sp
  let vars = map fst sp
  rhs <- quoteM rhs
  checkSolution m vars rhs

  let wrap :: Tm -> (Name, Maybe Tm) -> Tm
      wrap t (x, Nothing) = Lam x Expl t
      wrap t (x, Just a ) = LamTel x a t

  rhs <- local (vals .~ []) $ evalM $ foldl' wrap rhs sp
  mcxt %= M.insert m (Solved rhs)

newMetaEntry :: MetaEntry -> M cxt MId
newMetaEntry p = do
  St i ms <- get
  put $ St (i + 1) (M.insert i p ms)
  pure i

-- | Remove duplicate elements.
ordNubBy :: Ord b => (a -> b) -> [a] -> [a]
ordNubBy f = go S.empty where
  go s [] = []
  go s (a:as) | S.member (f a) s = go s as
              | otherwise        = a : go (S.insert (f a) s) as

newMetaSpine :: (HasVals cxt Vals, HasInfo cxt Info) => M cxt [(Name, Maybe Tm)]
newMetaSpine = do
  info <- ordNubBy fst <$> view info
  vals <- ordNubBy fst <$> view vals
  ms   <- use mcxt

  let go :: Info -> Vals -> [(Name, Maybe Tm)]
      go [] [] = []
      go ((x, i):is) (_:vs) = case i of
        Bound      -> (x, Nothing) : go is vs
        BoundTel a -> (x, Just (runEval (quote a) ms vs)) : go is vs
        Defined    -> go is vs
      go _ _ = error "impossible"

  pure $ go info vals

-- | Create fresh meta, return the meta applied to all bound variables in scope.
newMeta :: (HasVals cxt Vals, HasInfo cxt Info) => M cxt Tm
newMeta = do
  sp <- newMetaSpine
  m  <- newMetaEntry (Unsolved mempty)

  let go :: (Name, Maybe Tm) -> Tm -> Tm
      go (x, Nothing) t = App t (Var x) Expl
      go (x, Just a)  t = AppTel a t (Var x)

  pure $ foldr go (Meta m) sp


bindU x (UnifyCxt vs is p) =
  UnifyCxt ((x, Nothing):vs) ((x, Bound):is) p

telBindU x ~a (UnifyCxt vs is p) =
  UnifyCxt ((x, Nothing):vs) ((x, BoundTel a):is) p


unify :: Val -> Val -> UnifyM ()
unify = go where

  -- todo: more sophisticated unif here
  -- we could force spines even during unifying them,
  -- but here we only force it once in the beginning.
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
  go topT topU = do
    topT <- forceM topT
    topU <- forceM topU

    (freshTel :: Name -> Val -> (Name, UnifyM () -> UnifyM ())) <- do
      vs <- view vals
      pure $ \x a -> (fresh vs x, local (telBindU x a))

    (fresh :: Name -> (Name, UnifyM () -> UnifyM ())) <- do
      vs <- view vals
      pure $ \x -> (fresh vs x, local (bindU x))

    case (topT, topU) of
      (VLam (fresh -> (VVar -> x, dive)) i t, VLam _ i' t') | i == i'->
        dive $ join $ go <$> applyM t x <*> applyM t' x
      (VLam (fresh -> (VVar -> x, dive)) i t, u) ->
        dive $ join $ go <$> applyM t x <*> vAppM u x i
      (u, VLam (fresh -> (VVar -> x, dive)) i t) ->
        dive $ join $ go <$> vAppM u x i <*> applyM t x

      (VPi (fresh -> (VVar -> x, dive)) i a b, VPi _ i' a' b') -> do
        go a a'
        dive $ join $ go <$> applyM b x <*> applyM b' x

      (VU, VU) -> pure ()
      (VTel, VTel) -> pure ()
      (VRec a, VRec a') -> go a a'
      (VTEmpty, VTEmpty) -> pure ()
      (VTCons (fresh -> (VVar -> x, dive)) a as, VTCons _ a' as') -> do
        go a a'
        dive $ join $ go <$> applyM as x <*> applyM as' x

      (VTempty, VTempty) -> pure ()
      (VTcons t u, VTcons t' u') -> go t t' >> go u u'

      (VPiTel x a b, VPiTel _ a' b') -> do
        (VVar -> x, dive) <- pure $ freshTel x a
        go a a'
        dive $ join $ go <$> applyM b x <*> applyM b' x

      (VLamTel x a b, VLamTel _ a' b') -> do
        (VVar -> x, dive) <- pure $ freshTel x a
        go a a'
        dive $ join $ go <$> applyM b x <*> applyM b' x

      (VNe h sp, VNe h' sp') | h == h' ->
        goSp h h' sp sp'

      (t@(VNe (HMeta m) sp), t'@(VNe (HMeta m') sp')) ->
        if spLen sp > spLen sp'
        then solveMeta m sp t'
        else solveMeta m' sp' t

      (VNe (HMeta m) sp, t) -> solveMeta m sp t
      (t, VNe (HMeta m) sp) -> solveMeta m sp t

      (VPiTel x (VNe (HMeta a) sp) b, VPi (fresh -> (x1@(VVar -> vx1), dive)) Impl a' b') -> do
        m <- newMetaEntry (Unsolved mempty)
        let gamma v = VNe (HMeta m) (SApp sp v Expl)
        solveMeta a sp (VTCons x1 a' (\_ -> gamma))
        x2 <- Evaluation.fresh <$> view vals <*> pure (x ++ "2")
        dive $ join $
          go <$> (VPiTel x2 (gamma vx1) <$> hlamM (\ ~x2 -> apply b' (VTcons vx1 x2)))
             <*> applyM b' vx1

      (VPiTel x a b, t) -> do
        go a VTEmpty
        join $ go <$> applyM b VTempty <*> pure t

      (VPi (fresh -> (x1@(VVar -> vx1), dive)) Impl a' b', VPiTel x (VNe (HMeta a) sp) b) -> do
        m <- newMetaEntry (Unsolved mempty)
        let gamma v = VNe (HMeta m) (SApp sp v Expl)
        solveMeta a sp (VTCons x1 a' (\_ -> gamma))
        x2 <- Evaluation.fresh <$> view vals <*> pure (x ++ "2")
        dive $ join $
          go <$> applyM b' vx1
             <*> (VPiTel x2 (gamma vx1) <$> hlamM (\ ~x2 -> apply b' (VTcons vx1 x2)))

      (t, VPiTel x a b) -> do
        go VTEmpty a
        go t =<< applyM b VTempty

      (t, t') -> do
        t  <- quoteM t
        t' <- quoteM t'
        report $ UnifyError t t'

-- Elaboration
--------------------------------------------------------------------------------

bind :: Name -> VTy -> ElabCxt -> ElabCxt
bind x ~a (ElabCxt vs ts is p) =
  ElabCxt ((x, Nothing):vs) ((x, a):ts) ((x, Bound):is) p

telBind :: Name -> VTy -> ElabCxt -> ElabCxt
telBind x ~a (ElabCxt vs ts is p) =
  ElabCxt ((x, Nothing):vs) ((x, VRec a):ts) ((x, BoundTel a):is) p

define :: Name -> Val -> VTy -> ElabCxt -> ElabCxt
define x ~v ~a (ElabCxt vs ts is p) =
  ElabCxt ((x, Just v):vs) ((x, a):ts) ((x, Defined):is) p

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
            go (App t m Impl) =<< applyM b mv
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
              go (App t m Impl) =<< applyM b mv
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
            (Lam x i' <$> (check t =<< applyM b v))

        (t, VPi x Impl a b) -> do
          let x' = fresh x ++ "%"
          binding x' a $ Lam x' Impl <$> (check t =<< applyM b (VVar x'))

        (t, VNe (HMeta _) _) -> do
          x      <- use nextMId <&> \i -> fresh $ "Γ" ++ show i
          tel    <- newMeta
          telv   <- evalM tel
          (t, a) <- telBinding x telv $ infer MIYes t
          a      <- closeM x =<< (telBinding x telv $ quoteM a)

          embedUnifyM $ unify topA (VPiTel x telv a)

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
        (t, vty) <- infer insertion t
        (a, b) <- forceM vty >>= \case
          VPi x i' a b -> do
            unless (i == i') $
              report $ IcitMismatch i i'
            pure (a, b)
          vty@(VNe (HMeta m) sp) -> do
            x   <- fresh <$> view vals <*> pure "x"
            a   <- evalM =<< newMeta
            b   <- closeM x =<< binding x a newMeta
            embedUnifyM $ unify vty (VPi x i a b)
            pure (a, b)
          vty -> do
            ty <- quoteM vty
            report $ ExpectedFunction ty
        u   <- check u a
        ~vu <- evalM u
        bvu <- applyM b vu
        pure (App t u i, bvu)

      RLam _ _ Left{} _ ->
        report CannotInferNamedLam

      RLam x _ (Right i) t -> insertMetas ins $ do
        a      <- evalM =<< newMeta
        (t, b) <- binding x a $ infer MIYes t
        b      <- closeM x =<< (binding x a $ quoteM b)
        pure (Lam x i t, VPi x i a b)

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

elabCxt0 :: ElabCxt
elabCxt0 = ElabCxt [] [] [] (initialPos "(stdin)")
