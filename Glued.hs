
{-# language BangPatterns, LambdaCase, OverloadedStrings #-}
{-# language DataKinds, GADTs, TypeFamilies, MagicHash #-}
{-# language PatternSynonyms #-}

{-# options_ghc -fwarn-incomplete-patterns #-}

module Glued where

import Prelude hiding (pi)
import Control.Monad
import Control.Applicative
import Control.Monad.Except
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

-- Data
--------------------------------------------------------------------------------

-- Concrete
type QType = QTerm
data QTerm
  = QVar !String
  | QApp QTerm QTerm
  | QPi !String QType QTerm
  | QLam !String QTerm
  | QStar
  | QAnn QTerm QType

-- Abstract
type AType = ATerm
data ATerm
  = AVar !String
  | AApp ATerm ATerm -- ^ We can apply to 'Pi' as well.
  | APi !String AType ATerm
  | ALam !String AType ATerm
  | AStar
  | Close {-# unpack #-} !Closure

-- Weak head normal
data Whnf
  = VVar !String
  | Alpha !Int
  | VApp Whnf Whnf
  | VPi  !String !AType {-# unpack #-} !Closure
  | VLam !String !AType {-# unpack #-} !Closure
  | VStar

data Closure = C {
  _env  :: !Env,
  _body :: !ATerm }

data Glued = G {
  _unreduced :: {-# unpack #-} !Closure,
  _whnf      :: Whnf }

data Entry = E {
  _term :: {-# unpack #-} !Glued,
  _type :: {-# unpack #-} !Glued }

type Env = HashMap String Entry
type TM  = Either String

-- Reduction
--------------------------------------------------------------------------------

glued :: Env -> ATerm -> Glued
glued e t = G (C e t) (whnf e t)

whnf :: Env -> ATerm -> Whnf
whnf e = \case
  AApp f x -> case whnf e f of
    VLam v ty (C e' t) -> whnf (M.insert v (E (glued e x) (glued e ty)) e') t
    VPi  v ty (C e' t) -> whnf (M.insert v (E (glued e x) (glued e ty)) e') t
    f'                 -> VApp f' (whnf e x)
  AVar v         -> _whnf $ _term $ e ! v
  APi  v ty t    -> VPi  v ty (C e t)
  ALam v ty t    -> VLam v ty (C e t)
  AStar          -> VStar
  Close (C e' t) -> whnf e' t

quoteVar :: Env -> String -> AType -> Entry
quoteVar e v ty = E (G (C e (AVar v)) (VVar v)) (glued e ty)

-- TODO: eta-expansion
alpha :: Int -> Env -> AType -> Entry
alpha a e ty = E (G (C e (error "alpha")) (Alpha a)) (glued e ty)

nf :: Env -> ATerm -> ATerm
nf e t = quote (whnf e t)

quote :: Whnf -> ATerm
quote = \case
  VVar v            -> AVar v
  VApp f x          -> AApp (quote f) (quote x)
  VPi  v ty (C e t) -> APi  v (nf e ty) (nf (M.insert v (quoteVar e v ty) e) t)
  VLam v ty (C e t) -> ALam v (nf e ty) (nf (M.insert v (quoteVar e v ty) e) t)
  VStar             -> AStar
  Alpha{}           -> error "quote: Alpha in Whnf"


-- Equality without reduction
--------------------------------------------------------------------------------

termSemiEq :: Env -> Env -> Int -> ATerm -> ATerm -> Maybe Bool
termSemiEq e e' !b t t' = case (t, t') of

  (AVar v, AVar v') -> case (_whnf $ _term $ e ! v, _whnf $ _term $ e' ! v') of
    (Alpha b, Alpha b') -> Just (b == b')
    (x      , y       ) -> True <$ guard (ptrEq x y)
  (AVar{}, _) -> Nothing
  (_, AVar{}) -> Nothing

  (AApp f x, AApp f' x') ->
    True <$ do {guard =<< termSemiEq e e' b f f'; guard =<< termSemiEq e e' b x x'}
  (AApp{}, _) -> Nothing
  (_, AApp{}) -> Nothing

  (ALam v ty t, ALam v' ty' t') -> (&&) <$> termSemiEq e e' b ty ty' <*>
    (let al = alpha b e ty in termSemiEq (M.insert v al e) (M.insert v' al e') (b + 1) t t')
  (APi  v ty t, APi  v' ty' t') -> (&&) <$> termSemiEq e e' b ty ty' <*>
    (let al = alpha b e ty in termSemiEq (M.insert v al e) (M.insert v' al e') (b + 1) t t')
  (AStar, AStar) -> Just True
  _              -> Just False


-- Equality with reduction
--------------------------------------------------------------------------------

whnfEq :: Int -> Whnf -> Whnf -> Bool
whnfEq !b t t' = case (t, t') of
  (VVar v,   VVar v'   ) -> v == v'
  (VApp f x, VApp f' x') -> whnfEq b f f' && whnfEq b x x'
  (VLam v ty (C e t), VLam v' ty' (C e' t')) ->
    termEq e e' b ty ty' &&
    let al = alpha b e ty
    in termEq (M.insert v al e) (M.insert v' al e') (b + 1) t t'
  (VPi v ty (C e t), VPi v' ty' (C e' t')) ->
    termEq e e' 0 ty ty' &&
    let al = alpha b e ty
    in termEq (M.insert v al e) (M.insert v' al e') (b + 1) t t'
  (VStar, VStar) -> True
  _              -> False

termEq :: Env -> Env -> Int -> ATerm -> ATerm -> Bool
termEq e e' !b t t' = case (t, t') of

  (AVar v, AVar v') -> case (_whnf $ _term $ e ! v, _whnf $ _term $ e' ! v') of
    (Alpha b, Alpha b') -> b == b'
    (x      , y       ) -> ptrEq x y || continue

  (AApp f x, AApp f' x') ->
    maybe False id (liftA2 (&&) (termSemiEq e e' b f f') (termSemiEq e e' b x x'))
    || continue
  _ -> continue

  where continue = whnfEq b (whnf e t) (whnf e' t')

