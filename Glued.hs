
{-# language BangPatterns, LambdaCase, OverloadedStrings #-}
{-# language DataKinds, GADTs, TypeFamilies, MagicHash #-}
{-# language PatternSynonyms #-}

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
{-# inline ptrEq #-}

data Term
  = Neu !String [Term] -- ^ Spines.
  | Lam !String Type Term
  | Pi !String Type Term
  | Star
  | Close_ {-# unpack #-} !Closure -- ^ Doesn't appear in raw terms.
  | Ann Term Type

data Val
  = VLam !String Type {-# unpack #-} !Closure
  | VPi  !String Type {-# unpack #-} !Closure
  | VStar
  | VNeu !Int [Val] -- ^ This can be only an alpha-check var

pattern Close env t = Close_ (Closure env t)

type Type = Term

data Closure = Closure {
  _env  :: !Env,
  _body :: Term }

data Glued = Glued {
  _unreduced :: {-# unpack #-} !Closure,
  _whnf      :: Val }

data Entry
  = Entry {
    _term :: {-# unpack #-} !Glued,
    _type :: {-# unpack #-} !Glued }
  | Bound !Int {-# unpack #-} !Glued -- ^ for alpha-eq checking (with Glued type)

type Env = HashMap String Entry
type TM  = Either String

-- whnf
--------------------------------------------------------------------------------

glued :: Env -> Term -> Glued
glued e t = Glued (Closure e t) (whnf e t)

whnfNeu :: Env -> String -> [Term] -> Val
whnfNeu e v args = case e ! v of
  Entry t ty -> go e (_whnf t) args
  Bound i _  -> VNeu i (map (whnf e) args)
  where
    go e f []     = f
    go e f (x:xs) = case f of
      VLam v ty (Closure e' t) ->
        go e (whnf (M.insert v (Entry (glued e x) (glued e ty)) e') t) xs
      VNeu v args -> VNeu v (args ++ map (whnf e) (x:xs))

whnf :: Env -> Term -> Val
whnf e = \case
  Neu v args -> whnfNeu e v args
  Lam v ty t -> VLam v ty (Closure e t)
  Pi  v ty t -> VPi  v ty (Closure e t)
  Ann t ty   -> whnf e  t
  Close e' t -> whnf e' t
  Star       -> VStar

bound :: Int -> Env -> Type -> Entry
bound b e ty = Bound b (glued e ty)

-- Equality without reduction
--------------------------------------------------------------------------------

-- | Semidecide variable equality.
varEq :: Env -> Env -> String -> String -> Bool
varEq e e' v v' = case (e ! v, e' ! v') of
  (Bound i _, Bound i' _) -> i == i'
  (x        , y         ) -> ptrEq x y

-- | Semidecide neutral term equality.
neutralEq :: Env -> Env -> Int -> String -> String -> [Term] -> [Term] -> Bool
neutralEq e e' !b v v' args args' =
  varEq e e' v v' && maybe False and (zipWithM (termEq e e' b) args args')

-- | Try to decide unreduced term equality, or fall back to semidecision for
--   neutral terms.
termEq :: Env -> Env -> Int -> Term -> Term -> Maybe Bool
termEq e e' b t t' = case (t, t') of
  (Neu v args, Neu v' args')  -> True <$ guard (neutralEq e e' b v v' args args')
  (Lam v ty t, Lam v' ty' t') -> (&&) <$> termEq e e' b ty ty' <*>
    (let bnd = bound b e ty in termEq (M.insert v bnd e) (M.insert v' bnd e') (b + 1) t t')
  (Pi  v ty t, Pi  v' ty' t') -> (&&) <$> termEq e e' b ty ty' <*>
    (let bnd = bound b e ty in termEq (M.insert v bnd e) (M.insert v' bnd e') (b + 1) t t')
  (Star, Star)                -> Just True

  (Ann t ty, t')   -> termEq e e' b t t'
  (t, Ann t' ty')  -> termEq e e' b t t'
  (Close e t, t')  -> termEq e e' b t t'
  (t, Close e' t') -> termEq e e' b t t'

  _                -> Just False

-- Equality with reduction
--------------------------------------------------------------------------------

-- | Decide equality for whnf terms. Switch to term equality with lazy reduction
--   when going under constructors.
whnfEq :: Int -> Val -> Val -> Bool
whnfEq !b t t' = case (t, t') of
  (VNeu v args, VNeu v' args') -> v == v' && and (zipWith (whnfEq b) args args')
  (VLam v ty (Closure e t), VLam v' ty' (Closure e' t')) ->
    reducingEq e e' b ty ty' &&
    let bnd = bound b e ty
    in reducingEq (M.insert v bnd e) (M.insert v' bnd e') (b + 1) t t'
  (VPi v ty (Closure e t), VPi v' ty' (Closure e' t')) ->
    reducingEq e e' 0 ty ty' &&
    let bnd = bound b e ty
    in reducingEq (M.insert v bnd e) (M.insert v' bnd e') (b + 1) t t'
  (VStar, VStar) -> True
  _              -> False

-- | If both sides are neutral, try unreduced equality, else reduce to whnf and continue.
reducingEq :: Env -> Env -> Int -> Term -> Term -> Bool
reducingEq e e' !b t t' = case (t, t') of
  (Neu v args, Neu v' args') ->
       neutralEq e e' b v v' args args'
    || whnfEq b (whnfNeu e v args) (whnfNeu e v' args')
  (t, t') -> whnfEq b (whnf e t) (whnf e' t')


