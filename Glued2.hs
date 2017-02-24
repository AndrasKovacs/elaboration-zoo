
{-# language
  PatternSynonyms, BangPatterns, MagicHash,
  DataKinds, LambdaCase, ViewPatterns, TupleSections,
  TypeFamilies, GADTs, EmptyCase, OverloadedStrings #-}
{-# options_ghc -fwarn-incomplete-patterns #-}

module Glued4 where

import Prelude hiding (pi)
import Control.Monad
import Data.Either
import Control.Monad.Except
import GHC.Prim (reallyUnsafePtrEquality#)
import GHC.Types (isTrue#)
import Data.String

import Data.HashMap.Strict (HashMap, (!))
import qualified Data.HashMap.Strict as M

import qualified Debug.Trace as Trace

{-
  Concept:
    - eval to whnf don't have to carry around types
    - Elaborated Term and WTerm var-s carry their glued types
    - Bound variables have no term environment entries
        (this lets us know they're bound)
-}

tracing a    = Trace.traceShow a a
traceShow x  = Trace.traceShow x
traceShowM x = Trace.traceShowM x
trace        = Trace.trace
traceM x     = Trace.traceM x

type Var   = String
type Gen   = Int
type Depth = Int

data Raw
  = RVar !Var
  | RApp !Raw !Raw
  | RStar
  | RLam !Var !Raw
  | RPi !Var !Raw !Raw
  | RLet !Var !Raw !Raw !Raw

{-
  We have lots of GType annotations. These are all values that are
  necessarily computed during elaboration, so we might as well keep them around.
  Since all those types must be present in environments anyway, this
  doesn't cause additional space leak (and with closure conversion,
  which we don't yet have, space leak should be roughly the same as with
  STG machines).

  Compared to Glued3, the definitions here are significantly simpler,
  and the performance should be roughly the same or better (larger terms
  versus half-size entries in closures).

-}

data Term
  = Var !Var !GType
  | Gen !Gen
  | App !Term !Term WType -- note WType (App f (x : WType))
  | Star
  | Lam !Var !Term
  | Pi !Var !GType !Term
  | PiApp !Term !GTerm
  | Let !Var !GType !GTerm !Term

-- whnf term
data WTerm
  = WVar !Var !GType
  | WGen !Gen
  | WApp !WTerm WTerm WType -- note WType
  | WLam !Var !(GTerm -> WTerm)
  | WPi !Var !GType !(GTerm -> WTerm)
  | WStar

type Type  = Term
type WType = WTerm
data C a   = C {getEnv :: {-# unpack #-} !TmEnv, unC :: !a}
data GTerm = G {getC   :: {-# unpack #-} !(C Term), getW :: WTerm}
type GType = GTerm
type TmEnv = HashMap Var GTerm
type TyEnv = HashMap Var GType

type Env   = (TmEnv, TyEnv) -- TyCheckEnv
type M     = Either String  -- TyCheck monad

-- Env ops
--------------------------------------------------------------------------------

-- Insert (bound var : type)
(<:) :: (Var, GType) -> Env -> Env
(v, ty) <: (tenv, tyenv) = (tenv, M.insert v ty tenv)

-- Insert (term : type)
(<::) :: (Var, GTerm, GType) -> Env -> Env
(v, t, ty) <:: (tenv, tyenv) = (M.insert v t tenv, M.insert v ty tyenv)

-- Whnf
--------------------------------------------------------------------------------

wapp :: WTerm -> GTerm -> WType -> WTerm
wapp (WLam _ f) x ty = f x
wapp f          x ty = WApp f (getW x) ty

whnf :: TmEnv -> Term -> WTerm
whnf e = \case
  Var v ty    -> maybe (WVar v ty) getW (M.lookup v e)
  App f x ty  -> wapp (whnf e f) (glue e x) ty
  Lam v t     -> WLam v $ \gt -> whnf (M.insert v gt e) t
  Pi v a b    -> WPi v a $ \gt -> whnf (M.insert v gt e) b
  Star        -> WStar
  Let v _ a b -> whnf (M.insert v a e) b
  _           -> error "whnf: impossible"

glue :: TmEnv -> Term -> GTerm
glue e t = G (C e t) (whnf e t)

ggen :: Gen -> GTerm
ggen g = G (C mempty (Gen g)) (WGen g)

gvar :: Var -> GType -> GTerm
gvar v ty = G (C mempty (Var v ty)) (WVar v ty)

gstar :: GType
gstar = G (C mempty Star) WStar

-- Syntactic  equality
--------------------------------------------------------------------------------

ptrEq :: a -> a -> Bool
ptrEq !x !y = isTrue# (reallyUnsafePtrEquality# x y)
{-# inline ptrEq #-}

-- | Move top level Let bindings and reducible PiApp args into
--   the environment.
bindElim :: C Term -> C Term
bindElim (C !e !t) = case t of
  PiApp f x -> case bindElim (C e f) of
    C e (Pi v a b) -> C (M.insert v x e) b
    C e f          -> C e (PiApp f x)
  Let v t ty t' -> bindElim (C (M.insert v t e) t')
  _             -> C e t

varTerm :: Gen -> Depth -> C Var -> C Term -> Maybe Bool
varTerm g d (C e v) t' = do
  guard $ d > 0
  t <- getC <$> M.lookup v e
  synEqN g (d - 1) t t'

varVar :: Gen -> Depth -> C Var -> C Var -> GType -> Maybe Bool
varVar !g !d (C e v) (C e' v') ty = case (M.lookup v e, M.lookup v' e') of
  (Nothing, Nothing) -> Just (v == v')
  (Just t,  Nothing) -> synEqN g (d - 1) (getC t) (C e' (Var v' ty))
  (Nothing, Just t') -> synEqN g (d - 1) (C e (Var v ty)) (getC t')
  (Just t, Just t') | ptrEq t t' -> Just True
                    | d == 0     -> Nothing
                    | otherwise  -> synEqN g (d - 1) (getC t) (getC t')

-- | Try to decide equality by doing n-depth delta-reduction and PiApp/Let substitution.
--   Beta reduction or eta expanision are *not* performed.
--   Returns 'Nothing' if equality can't be decided this way.
synEqN :: Gen -> Depth -> C Term -> C Term -> Maybe Bool
synEqN !g !d (bindElim -> C e t) (bindElim -> C e' t') = case (t, t') of
  (Star, Star) -> Just True

  (Lam v t, Lam v' t') -> let !gen = ggen g in
    synEqN (g + 1) d (C (M.insert v gen e) t) (C (M.insert v' gen e') t')

  (Pi v a b, Pi v' a' b') -> let !gen = ggen g in
    (&&) <$> synEqN  g d (getC a) (getC a') <*>
    synEqN (g + 1) d (C (M.insert v gen e) t) (C (M.insert v' gen e') t')

  (App f x _, App f' x' _) -> True <$ do
    guard =<< synEqN g d (C e f) (C e' f')
    guard =<< synEqN g d (C e x) (C e' x')

  (Var v ty, Var v' _) -> varVar g d (C e v) (C e' v') ty
  (Var v _, t') -> varTerm g d (C e v) (C e' t')
  (t, Var v' _) -> varTerm g d (C e' v') (C e t)

  (App{}, _) -> Nothing
  (_, App{}) -> Nothing
  _          -> Just False

-- Beta-eta conversion check
--------------------------------------------------------------------------------

conv :: WType -> WType -> Bool
conv = go 0 WStar where

  go :: Gen -> WType -> WTerm -> WTerm -> Bool
  go !g _ WStar WStar = True

  go g _ (WPi _ a b) (WPi _ a' b') = let gen = ggen g in
    go g WStar (getW a) (getW a') && go (g + 1) WStar (b gen) (b' gen)

  -- this is very nice, comes from page 22 of Ulf Norell's Agda thesis
  go g (WPi _ a b) t t' = let gen = ggen g in
    go (g + 1) (b gen) (wapp t gen (getW a)) (wapp t gen (getW a))

  go g _ t t' = neu g t t'

  neu :: Gen -> WTerm -> WTerm -> Bool
  neu !g (WApp f x ty) (WApp f' x' _) = go g x x' ty && neu g f f'
  neu  g (WVar v _)    (WVar v' _)    = v == v'
  neu  g (WGen v)      (WGen v')      = v == v'
  neu  _ _             _              = False


-- Check & infer + elaborate in the meantime
--------------------------------------------------------------------------------

check :: Env -> Raw -> WType -> M Term
check e t ty = case (t, ty) of
  (RLam v t, WPi _ a b) ->
    Lam v <$> check ((v, a) <: e) t (b (gvar v a))
  _ -> do
    (t, has) <- infer e t
    unless (conv (getW has) ty) $ throwError "type mismatch"
    pure t

gcheck :: Env -> Raw -> WType -> M GTerm
gcheck e t ty = glue (snd e) <$> check e t ty

infer :: Env -> Raw -> M (Term, GType)
infer e = \case
  RVar v -> let !ty = fst e ! v in pure (Var v ty, ty)
  RStar  -> pure (Star, gstar)
  RPi v a b -> do
    a <- gcheck e a WStar
    b <- check ((v, a) <: e) b WStar
    pure (Pi v a b, gstar)
  RLam v t -> throwError "can't infer type for lambda"
  RLet v ty a b -> do
    ta       <- gcheck e ty WStar
    a        <- gcheck e a (getW ta)
    (b, tb)  <- infer ((v, a, ta) <:: e) b
    pure (Let v ta a b, tb)
  RApp f x -> do
    (f, tf) <- infer e f
    case getW tf of
      WPi v ta tb -> do
        gx <- gcheck e x (getW ta)
        pure (App f (unC $ getC gx) (getW ta), G (C (snd e) (PiApp f gx)) (tb gx))
      _ -> throwError "can't apply non-function"
