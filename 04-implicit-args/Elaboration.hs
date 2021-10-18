
module Elaboration (check, infer) where

import Control.Exception
import Control.Monad
import Data.IORef

import qualified Data.IntMap as IM

import Common
import Cxt
import Errors
import Evaluation
import Metacontext
import Syntax
import Unification
import Value

import qualified Presyntax as P


-- Elaboration
--------------------------------------------------------------------------------

freshMeta :: Cxt -> IO Tm
freshMeta cxt = do
  m <- readIORef nextMeta
  writeIORef nextMeta (m + 1)
  modifyIORef' mcxt $ IM.insert m Unsolved
  pure $ InsertedMeta (MetaVar m) (bds cxt)

unifyCatch :: Cxt -> Val -> Val -> IO ()
unifyCatch cxt t t' =
  unify (lvl cxt) t t'
  `catch` \UnifyError ->
    throwIO $ Error cxt $ CantUnify (quote (lvl cxt) t) (quote (lvl cxt) t')

-- | Insert fresh implicit applications.
insert' :: Cxt -> IO (Tm, VTy) -> IO (Tm, VTy)
insert' cxt act = go =<< act where
  go (t, va) = case force va of
    VPi x Impl a b -> do
      m <- freshMeta cxt
      let mv = eval (env cxt) m
      go (App t m Impl, b $$ mv)
    va -> pure (t, va)

-- | Insert fresh implicit applications to a term which is not
--   an implicit lambda (i.e. neutral).
insert :: Cxt -> IO (Tm, VTy) -> IO (Tm, VTy)
insert cxt act = act >>= \case
  (t@(Lam _ Impl _), va) -> pure (t, va)
  (t               , va) -> insert' cxt (pure (t, va))

-- | Insert fresh implicit applications until we hit a Pi with
--   a particular binder name.
insertUntilName :: Cxt -> Name -> IO (Tm, VTy) -> IO (Tm, VTy)
insertUntilName cxt name act = go =<< act where
  go (t, va) = case force va of
    va@(VPi x Impl a b) -> do
      if x == name then
        pure (t, va)
      else do
        m <- freshMeta cxt
        let mv = eval (env cxt) m
        go (App t m Impl, b $$ mv)
    _ ->
      throwIO $ Error cxt $ NoNamedImplicitArg name

check :: Cxt -> P.Tm -> VTy -> IO Tm
check cxt t a = case (t, force a) of
  (P.SrcPos pos t, a) ->
    check (cxt {pos = pos}) t a

  -- If the icitness of the lambda matches the Pi type, check as usual
  (P.Lam x i t, VPi x' i' a b) | either (\x -> x == x' && i' == Impl) (==i') i -> do
    Lam x i' <$> check (bind cxt x a) t (b $$ VVar (lvl cxt))

  -- Otherwise if Pi is implicit, insert a new implicit lambda
  (t, VPi x Impl a b) -> do
    Lam x Impl <$> check (newBinder cxt x a) t (b $$ VVar (lvl cxt))

  (P.Let x a t u, a') -> do
    a <- check cxt a VU
    let ~va = eval (env cxt) a
    t <- check cxt t va
    let ~vt = eval (env cxt) t
    u <- check (define cxt x vt va) u a'
    pure (Let x a t u)

  (P.Hole, a) ->
    freshMeta cxt

  (t, expected) -> do
    (t, inferred) <- insert cxt $ infer cxt t
    unifyCatch cxt expected inferred
    pure t

infer :: Cxt -> P.Tm -> IO (Tm, VTy)
infer cxt = \case
  P.SrcPos pos t ->
    infer (cxt {pos = pos}) t

  P.Var x -> do
    let go ix (types :> (x', origin, a))
          | x == x' && origin == Source = pure (Var ix, a)
          | otherwise                   = go (ix + 1) types
        go ix [] =
          throwIO $ Error cxt $ NameNotInScope x

    go 0 (types cxt)

  P.Lam x (Right i) t -> do
    a <- eval (env cxt) <$> freshMeta cxt
    let cxt' = bind cxt x a
    (t, b) <- insert cxt' $ infer cxt' t
    pure (Lam x i t, VPi x i a $ closeVal cxt b)

  P.Lam x Left{} t ->
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
        a <- eval (env cxt) <$> freshMeta cxt
        b <- Closure (env cxt) <$> freshMeta (bind cxt "x" a)
        unifyCatch cxt tty (VPi "x" i a b)
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
    (u, b) <- infer (define cxt x vt va) u
    pure (Let x a t u, b)

  P.Hole -> do
    a <- eval (env cxt) <$> freshMeta cxt
    t <- freshMeta cxt
    pure (t, a)
