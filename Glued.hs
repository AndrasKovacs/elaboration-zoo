
{-# language BangPatterns, LambdaCase, OverloadedStrings #-}
{-# language DataKinds, GADTs, TypeFamilies, MagicHash #-}

module Glued where

import Prelude hiding (pi)
import Control.Monad
import Data.Either
import GHC.Prim (reallyUnsafePtrEquality#)
import GHC.Types (isTrue#)

import Data.HashMap.Strict (HashMap, (!))
import qualified Data.HashMap.Strict as M

import Syntax (RawTerm)
import qualified Syntax as S

ptrEq :: a -> a -> Bool
ptrEq x y = isTrue# (reallyUnsafePtrEquality# x y)

-- | We have the same type for unreduced and reduced terms.
data Term
  = Var !String
  | App Term Term
  | Lam !String Type Term
  | Pi !String Type Term
  | Star
  | Close_ {-# unpack #-} !Closure -- this doesn't appear in raw terms
  | Ann Term Type

pattern Close env t = Close_ (Closure env t)

type Type = Term

data Closure = Closure {
  _env  :: !Env,
  _body :: Term }

data Glued = Glued {
  _unreduced :: {-# unpack #-} !Closure,
  _whnf      :: Term }

data Entry
  = Bound !Int
  | Entry {
      _term :: {-# unpack #-} !Glued,
      _type :: {-# unpack #-} !Glued }
  
type Env = HashMap String Entry
type TM  = Either String

glued :: Env -> Term -> Glued
glued env t = Glued (Closure env t) (whnf env t)

whnf :: Env -> Term -> Term
whnf env = \case
  Var v   -> _whnf $ _term $ env ! v
  App f x -> case whnf env f of
    Lam v ty (Close env' t) ->
      whnf (M.insert v (Entry (glued env x) (glued env ty)) env') t
    f' -> App f' (whnf env x)
  Lam v ty t   -> Lam v ty (Close env t)
  Pi  v ty t   -> Pi  v ty (Close env t)
  Ann t ty     -> whnf env t
  Close env' t -> whnf env' t
  Star         -> Star

-- | Non-reducing term equality. Semidecision.
termEq :: Env -> Env -> Int -> Term -> Term -> Bool
termEq e e' !b t t' = case (t, t') of
  (Var v, Var v') -> case (e ! v, e' ! v') of
    (Bound i, Bound i') -> i == i'
    (x      , y       ) -> ptrEq x y
  (App f x, App f' x')        -> termEq e e' b f f' && termEq e e' b x x'
  (Lam v ty t, Lam v' ty' t') -> termEq e e' b ty ty' &&
    let bnd = Bound b in termEq (M.insert v bnd e) (M.insert v' bnd e') (b + 1) t t'
  (Pi v ty t, Pi v' ty' t') -> termEq e e' b ty ty' &&
    let bnd = Bound b in termEq (M.insert v bnd e) (M.insert v' bnd e') (b + 1) t t'
  (Ann t ty, t')   -> termEq e e' b t t'
  (t, Ann t' ty')  -> termEq e e' b t t'
  (Close e t, t')  -> termEq e e' b t t'
  (t, Close e' t') -> termEq e e' b t t'
  (Star, Star)     -> True
  _                -> False

reducingEq :: Env -> Env -> Int -> Term -> Term -> Bool
reducingEq = undefined

-- | Whnf equality
whnfEq :: Env -> Env -> Int -> Term -> Term -> Bool
whnfEq e e' !b t t' = case (t, t') of
  (Var v, Var v') -> case (e ! v, e' ! v') of
    (Bound i, Bound i') -> i == i'
    (Entry (Glued (Closure e t) _) _, Entry (Glued (Closure e' t') _) _) ->
      whnfEq e e' b t t'
    _  -> False
  (App f x, App f' x') -> whnfEq e e' b f f' && whnfEq e e' b x x'
  (Lam v ty (Close e t), Lam v' ty' (Close e' t')) -> reducingEq e e' b ty ty' &&
    let bnd = Bound b in reducingEq (M.insert v bnd e) (M.insert v' bnd e') (b + 1) t t'
  (Pi v ty (Close e t), Lam v' ty' (Close e' t')) -> reducingEq e e' b ty ty' &&
    let bnd = Bound b in reducingEq (M.insert v bnd e) (M.insert v' bnd e') (b + 1) t t'    
    
  

