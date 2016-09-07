
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

  --> type checking env is not the same as evaluating env
  --> we could re-typecheck Terms without any environment at all
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

data Term
  = Var !Var !GType
  | Gen !Gen !GType
  | App !Term !Term WType
  | Star
  | Lam !Var !Term
  | Pi !Var !Type !Term
  | PiApp !Term !GTerm

data WTerm
  = WVar !Var
  | WGen !Gen
  | WApp !WTerm WTerm WType
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
type Env   = (TmEnv, TyEnv)
type M     = Either String

-- Whnf
--------------------------------------------------------------------------------

wapp :: WTerm -> GTerm -> WType -> WTerm
wapp (WLam _ f) x ty = f x
wapp f          x ty = WApp f (getW x) ty

whnf :: TmEnv -> Term -> WTerm
whnf e = \case
  Var v ty   -> getW $ e ! v
  App f x ty -> wapp (whnf e f) (glue e x) ty
  Lam v t    -> WLam v $ \gt -> whnf (M.insert v gt e) t
  Pi v a b   -> WPi v (glue e a) $ \gt -> whnf (M.insert v gt e) b
  Star       -> WStar
  _          -> error "whnf: impossible"

glue :: TmEnv -> Term -> GTerm
glue e t = G (C e t) (whnf e t)

gen :: Gen -> GType -> GTerm
gen g gty = G (C mempty (Gen g gty)) (WGen g)

-- Conversion check
--------------------------------------------------------------------------------

conv :: WType -> WType -> Bool
conv = go 0 WStar where

  go :: Gen -> WType -> WTerm -> WTerm -> Bool
  go g _ WStar WStar = True

  go g _ (WPi _ a b) (WPi _ a' b') = let gvar = gen g a in
    go g WStar (getW a) (getW a') && go (g + 1) WStar (b gvar) (b' gvar)

  go g (WPi _ a b) t t' = let gvar = gen g a in
    go (g + 1) (b gvar) (wapp t gvar (getW a)) (wapp t gvar (getW a))

  go g _ t t' = neu g t t'

  neu :: Gen -> WTerm -> WTerm -> Bool
  neu g (WApp f x ty) (WApp f' x' _) = neu g f f' && go g x x' ty
  neu g (WVar v)      (WVar v')      = v == v'
  neu g (WGen v)      (WGen v')      = v == v'
  neu _ _             _              = False

-- Check & infer
--------------------------------------------------------------------------------

-- check :: GEnv -> Raw -> GType -> M Term
-- check (we, ge) rt gty = case (rt, gty) of
--   (RLam v t, G (C ge' ty) (WPi v' a wa wb)) -> do

--     t' <- check
--       (M.insert v (WVar v wa) we , M.insert v (E undefined _) ge)
--       t (G _ (wb (WVar v wa)))
--     undefined
