
{-# language PatternSynonyms, BangPatterns, MagicHash, LambdaCase, ViewPatterns #-}
{-# language OverloadedStrings, TypeFamilies, GADTs, EmptyCase #-}
{-# options_ghc -fwarn-incomplete-patterns #-}

module Glued3 where

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

type AlphaVar = Int
type Var = Text

type Type = Term
data Term
  = Var !Var
  | Alpha !AlphaVar
  | App !Term !Term
  | PiApp !Term {-# unpack #-} !Closure
  | Pi !Var !Type !Type
  | Lam !Var !Term
  | Let !Var !Type !Term !Term
  | Star

-- whnf
type WType = WTerm
data WTerm
  = WVar !Var
  | WAlpha !AlphaVar
  | WApp !WTerm WTerm
  | WPi {-# unpack #-} !PiBind
  | WLam {-# unpack #-} !LamBind
  | WStar

data GTerm   = G !Closure !WTerm
type GType   = GTerm
data Closure = C !Env !Term
data Entry   = E {-# unpack #-} !GTerm {-# unpack #-} !GType
data LamBind = LamBind !Env !Var !Term
data PiBind  = PiBind !Env !Var !Type WType !Term
type Env     = HashMap Var Entry
type M       = Either String

instance IsString Term   where fromString = Var . fromString
instance IsString WTerm  where fromString = WVar . fromString

inst :: LamBind -> PiBind -> GTerm -> (WTerm, WType)
inst (LamBind e v t) (PiBind e' v' a wa b) x =
  let glued_a = G (C e' a) wa in
  (whnf (M.insert v (E x glued_a) e) t, whnf (M.insert v' (E x glued_a) e') b)

instPi :: PiBind -> GTerm -> WType
instPi (PiBind e v a wa b) t' = whnf (M.insert v (E t' (G (C e a) wa)) e) b

--------------------------------------------------------------------------------

glued :: Env -> Term -> GTerm
glued e t = G (C e t) (whnf e t)

whnfApp :: Env -> Term -> (WTerm, WType)
whnfApp e = \case
  Var v -> let E (G _ t) (G _ ty) = e ! v in (t, ty)
  App f x -> case whnfApp e f of
    (WLam lam, WPi pi) -> inst lam pi (glued e x)
    (f       , WPi pi) -> (WApp f (whnf e x), instPi pi (glued e x))
    _                  -> error "whnfApp: impossible"
  _ -> error "whnfApp: impossible"
    
whnf :: Env -> Term -> WTerm
whnf e = \case
  Var v     -> let E (G _ t) _ = e ! v in t
  App f x   -> fst $ whnfApp e (App f x)
  Pi v a b  -> WPi (PiBind e v a (whnf e a) b)
  Lam v t   -> WLam (LamBind e v t)
  PiApp f (C e x) -> case whnf e f of
    WPi pi -> instPi pi (glued e x)
    _      -> error "whnf: impossible"
  Star -> WStar
  Let v t ty t' -> whnf (M.insert v (E (glued e t) (glued e ty)) e) t'
  _ -> error "whnf: impossible"


  
  







