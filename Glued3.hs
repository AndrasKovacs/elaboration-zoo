
{-# language
  PatternSynonyms, BangPatterns, MagicHash,
  DataKinds, LambdaCase, ViewPatterns #-}
{-# language OverloadedStrings, TypeFamilies, GADTs, EmptyCase #-}
{-# options_ghc -fwarn-incomplete-patterns #-}

module Glued2 where

import Prelude hiding (pi)
import Data.String
import Control.Monad
import Control.Applicative
import Control.Monad.Except
import Data.Either
import GHC.Prim (reallyUnsafePtrEquality#)
import GHC.Types (isTrue#)

import Data.Text (Text)
import qualified Data.Text as T

import Data.HashMap.Strict (HashMap, (!))
import qualified Data.HashMap.Strict as M

ptrEq :: a -> a -> Bool
ptrEq !x !y = isTrue# (reallyUnsafePtrEquality# x y)
{-# inline ptrEq #-}

type Var = Text
type Gen = Int

data PiSp
  = Pi !Var !Term !Term
  | PiApp !PiSp {-# unpack #-} !Closure -- this shouldn't be in raw terms
  deriving Show

type Type = Term
data Term
  = Sp !Var ![Term]
  | PiSp !PiSp
  | Let !Var !Term !Term !Term
  | Star
  | Lam !Var !Term
  deriving Show

type WType = WTerm

data Neu
  = WVar !Var
  | WApp !Neu WTerm
  deriving Show
  
data WTerm
  = Neu !Neu
  | WPi  {-# unpack #-} !PiBind
  | WLam {-# unpack #-} !LamBind
  | WStar
  deriving Show

data Closure = C !Env !Term deriving Show
data GTerm   = G {-# unpack #-} !Closure !WTerm deriving Show
type GType   = GTerm
data Entry   = E {-# unpack #-} !GTerm {-# unpack #-} !GType deriving Show
type Env     = HashMap Var Entry
data LamBind = LamBind !Env !Var !Term deriving Show
data PiBind  = PiBind !Env !Var !Type WType !Term deriving Show
type M       = Either String

inst :: LamBind -> PiBind -> GTerm -> (WTerm, WType)
inst (LamBind e v t) (PiBind e' v' a wa b) x =
  let ga = G (C e' a) wa in
  (whnf (M.insert v (E x ga) e) t, whnf (M.insert v' (E x ga) e') b)

instPi :: PiBind -> GTerm -> WType
instPi (PiBind e v a wa b) t' = whnf (M.insert v (E t' (G (C e a) wa)) e) b

glued :: Env -> Term -> GTerm
glued !e !t = G (C e t) (whnf e t)

whnfSp :: Env -> (WTerm, WType) -> [Term] -> (WTerm, WType)
whnfSp !e (t, ty) []      = (t, ty)
whnfSp  e (t, ty) (t':ts) = case (t, ty) of
  (WLam lam, WPi pi) -> whnfSp e (inst lam pi (glued e t')) ts
  (Neu t   , WPi pi) -> whnfSp e (Neu (WApp t (whnf e t')), instPi pi (glued e t')) ts
  _                  -> error "whnfSp: impossible"

whnfPiSp :: Env -> PiSp -> WTerm
whnfPiSp !e (Pi v a b)         = WPi (PiBind e v a (whnf e a) b)
whnfPiSp  e (PiApp p (C e' t)) = case whnfPiSp e p of
  WPi pi -> instPi pi (glued e' t)
  _      -> error "whnfPiSp: impossible"

whnf :: Env -> Term -> WTerm
whnf !e = \case
  Sp v ts       -> let E (G _ t) (G _ ty) = e ! v in fst $ whnfSp e (t, ty) ts
  PiSp p        -> whnfPiSp e p
  Lam v t       -> WLam (LamBind e v t)
  Star          -> WStar
  Let v t ty t' -> whnf (M.insert v (E (glued e t) (glued e ty)) e) t'

quote :: WTerm -> Term
quote = \case
  

  

