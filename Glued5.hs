
{-# language
  PatternSynonyms, BangPatterns, MagicHash,
  DataKinds, LambdaCase, ViewPatterns, TupleSections,
  TypeFamilies, GADTs, EmptyCase, OverloadedStrings #-}
{-# options_ghc -fwarn-incomplete-patterns #-}

module Glued5 where

import Prelude hiding (pi)
import Control.Monad
import Data.Either
import Control.Monad.Except
import GHC.Prim (reallyUnsafePtrEquality#)
import GHC.Types (isTrue#)
import Data.String

import Data.HashMap.Strict (HashMap, (!))
import qualified Data.HashMap.Strict as M

{-
  I'm just testing whether we can separate Term and Value
  environments, and only use the former in Term closures
  and the lattern in Value closures.

  For simplicity we don't have eta conversion here.
-}

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

data Term
  = Var !Var
  | Gen !Gen
  | App !Term !Term
  | Star
  | Lam !Var !Term
  | Pi !Var !Term !Term
  | PiApp !Term !Term
  | Let !Var !Term !Term !Term

-- whnf term
data WTerm
  = WVar !Var 
  | WGen !Gen
  | WApp !WTerm WTerm
  | WLam !Var !(WTerm -> WTerm)
  | WPi !Var !WType !(WTerm -> WTerm)
  | WStar

type Type  = Term
type WType = WTerm
type TEnv  = [(Var, Term)] -- WRONG!! must have (C Term) as value
type WEnv  = [(Var, WTerm)]
data C a   = C {getEnv :: {-# unpack #-} !TEnv, unC :: !a}
type M     = Either String

-- Env ops
--------------------------------------------------------------------------------

-- -- Insert (bound var : type)
-- (<:) :: (Var, GType) -> Env -> Env
-- (v, ty) <: (tenv, tyenv) = (tenv, M.insert v ty tenv)

-- -- Insert (term : type)
-- (<::) :: (Var, GTerm, GType) -> Env -> Env
-- (v, t, ty) <:: (tenv, tyenv) = (M.insert v t tenv, M.insert v ty tyenv)

-- Whnf
--------------------------------------------------------------------------------

wapp :: WTerm -> WTerm -> WTerm 
wapp (WLam _ f) x = f x
wapp f          x = WApp f x

whnf :: WEnv -> Term -> WTerm
whnf e = \case
  Var v       -> maybe (WVar v) id (lookup v e)
  App f x     -> wapp (whnf e f) (whnf e x)
  Lam v t     -> WLam v $ \a -> whnf ((v, a):e) t
  Pi v a b    -> WPi v (whnf e a) $ \a' -> whnf ((v, a'):e) b
  Let v a _ b -> whnf ((v, whnf e a):e) b
  Star        -> WStar
  _           -> undefined

-- Syntactic  equality
--------------------------------------------------------------------------------

lookupC :: Var -> TEnv -> Maybe (C Term)
lookupC v ((v',t) :ts) | v == v'   = Just (C ts t)
                       | otherwise = lookupC v ts
lookupC _ _ = Nothing                       

ptrEq :: a -> a -> Bool
ptrEq !x !y = isTrue# (reallyUnsafePtrEquality# x y)

cEq :: C a -> C a -> Bool
cEq (C e a) (C e' a') = ptrEq e e' && ptrEq a a'

-- | Move top level Let bindings and reducible PiApp args into
--   the environment.
bindElim :: C Term -> C Term
bindElim (C !e !t) = case t of
  PiApp f x -> case bindElim (C e f) of
    C e (Pi v a b) -> C ((v, a):e) b
    C e f          -> C e (PiApp f x)
  Let v t ty t' -> bindElim (C ((v, t):e) t')
  _             -> C e t

varTerm :: Gen -> Depth -> C Var -> C Term -> Maybe Bool
varTerm g d (C e v) t' = do
  guard $ d > 0
  t <- lookupC v e
  synEqN g (d - 1) t t'

varVar :: Gen -> Depth -> C Var -> C Var -> Maybe Bool
varVar !g !d (C e v) (C e' v') = case (lookupC v e, lookupC v' e') of
  (Nothing, Nothing) -> Just (v == v')
  (Just c,  Nothing) -> synEqN g (d - 1) c (C e' (Var v'))
  (Nothing, Just c') -> synEqN g (d - 1) (C e (Var v)) c'
  (Just c,  Just c') | cEq c c'   -> Just True
                     | d == 0     -> Nothing
                     | otherwise  -> synEqN g (d - 1) c c'

synEqN :: Gen -> Depth -> C Term -> C Term -> Maybe Bool
synEqN !g !d (bindElim -> C e t) (bindElim -> C e' t') = case (t, t') of
  (Star, Star) -> Just True

  (Lam v t, Lam v' t') -> let !gen = Gen g in
    synEqN (g + 1) d (C ((v, gen) : e) t) (C ((v', gen): e') t')

  (Pi v a b, Pi v' a' b') -> let !gen = Gen g in
    (&&) <$> synEqN  g d (C e a) (C e a') <*>
    synEqN (g + 1) d (C ((v, gen): e) t) (C ((v', gen): e') t')

  (App f x, App f' x') -> True <$ do
    guard =<< synEqN g d (C e f) (C e' f')
    guard =<< synEqN g d (C e x) (C e' x')

  (Var v, Var v' ) -> varVar g d (C e v) (C e' v')
  (Var v, t'     ) -> varTerm g d (C e v) (C e' t')
  (t,     Var v' ) -> varTerm g d (C e' v') (C e t)
  (App{}, _      ) -> Nothing
  (_,     App{}  ) -> Nothing
  _                -> Just False

-- Beta-eta conversion check
--------------------------------------------------------------------------------

conv :: WTerm -> WTerm -> Bool
conv = go 0 where
  go !g WStar       WStar          = True
  go  g (WLam v t)  (WLam v' t')   = let !gen = WGen g in go (g + 1) (t gen) (t' gen)
  go  g (WPi v a b) (WPi v' a' b') = go g a a' && let !gen = WGen g in go (g + 1) (b gen) (b' gen)
  go  g (WVar v)    (WVar v')      = v == v'
  go  g (WGen v)    (WGen v')      = v == v'
  go  g (WApp f x)  (WApp f' x')   = go g f f' && go g x x'
  go  _ _           _              = False


-- Check & infer + elaborate in the meantime
--------------------------------------------------------------------------------

-- (type, term)
type Checking a = TEnv -> WEnv -> TEnv -> WEnv -> a

-- check :: Checking (Raw -> WType -> M Term)
-- check ts wts tms wtms t ty = case (t, ty) of
--   (RLam v t, WPi _ a b) ->
--     Lam v <$> check ((v, a):

-- check :: Env -> Raw -> WType -> M Term
-- check e t ty = case (t, ty) of
--   (RLam v t, WPi _ a b) ->
--     Lam v <$> check ((v, a) <: e) t (b (gvar v a))
--   _ -> do
--     (t, has) <- infer e t
--     unless (conv (getW has) ty) $ throwError "type mismatch"
--     pure t

-- gcheck :: Env -> Raw -> WType -> M GTerm
-- gcheck e t ty = glue (snd e) <$> check e t ty

-- infer :: Env -> Raw -> M (Term, GType)
-- infer e = \case
--   RVar v -> let !ty = fst e ! v in pure (Var v ty, ty)
--   RStar  -> pure (Star, gstar)
--   RPi v a b -> do
--     a <- gcheck e a WStar
--     b <- check ((v, a) <: e) b WStar
--     pure (Pi v a b, gstar)
--   RLam v t -> throwError "can't infer type for lambda"
--   RLet v ty a b -> do
--     ta       <- gcheck e ty WStar
--     a        <- gcheck e a (getW ta)
--     (b, tb)  <- infer ((v, a, ta) <:: e) b
--     pure (Let v ta a b, tb)
--   RApp f x -> do
--     (f, tf) <- infer e f
--     case getW tf of
--       WPi v ta tb -> do
--         gx <- gcheck e x (getW ta)
--         pure (App f (unC $ getC gx) (getW ta), G (C (snd e) (PiApp f gx)) (tb gx))
--       _ -> throwError "can't apply non-function"
