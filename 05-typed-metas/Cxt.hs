
module Cxt where

import qualified Data.Map.Strict as M

import Common
import Evaluation
import Pretty
import Syntax
import Value

-- Elaboration context
--------------------------------------------------------------------------------

data NameOrigin = Inserted | Source deriving Eq

type Types = [(String, NameOrigin, VTy)]

data Cxt = Cxt {
    env         :: Env
  , lvl         :: Lvl
  , metaClosure :: MetaClosure
  , srcNames    :: M.Map Name (Lvl, VTy)
  , pos         :: SourcePos
  }

names :: Cxt -> [Name]
names = go . metaClosure where
  go Nil               = []
  go (Define ms x _ _) = x: go ms
  go (Bind ms x _)     = x: go ms

showVal :: Cxt -> Val -> String
showVal cxt v =
  prettyTm 0 (names cxt) (quote (lvl cxt) v) []

showTm :: Cxt -> Tm -> String
showTm cxt t = prettyTm 0 (names cxt) t []

instance Show Cxt where
  show = show . names

emptyCxt :: SourcePos -> Cxt
emptyCxt = Cxt [] 0 Nil mempty

-- | Extend Cxt with a bound variable.
bind :: Cxt -> Name -> VTy -> Cxt
bind (Cxt env l mcl ns pos) x ~a =
  Cxt (env :> VVar l) (l + 1) (Bind mcl x (quote l a)) (M.insert x (l, a) ns) pos

-- | Insert a new binding.
newBinder :: Cxt -> Name -> VTy -> Cxt
newBinder (Cxt env l mcl ns pos) x ~a =
  Cxt (env :> VVar l) (l + 1) (Bind mcl x (quote l a)) ns pos

-- | Extend Cxt with a definition.
define :: Cxt -> Name -> Tm -> Val -> Ty -> VTy -> Cxt
define (Cxt env l mcl ns pos) x ~t ~vt ~a ~va  =
  Cxt (env :> vt) (l + 1) (Define mcl x a t) (M.insert x (l, va) ns) pos

-- | closeVal : (Γ : Con) → Val (Γ, x : A) B → Closure Γ A B
closeVal :: Cxt -> Val -> Closure
closeVal cxt t = Closure (env cxt) (quote (lvl cxt + 1) t)
