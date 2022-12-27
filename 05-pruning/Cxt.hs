
module Cxt where

import qualified Data.Map.Strict as M

import Common
import Evaluation
import Pretty
import Syntax
import Value

-- Elaboration context
--------------------------------------------------------------------------------

data Cxt = Cxt {                       -- Used for:
    env       :: Env                   -- evaluation
  , lvl       :: Lvl                   -- going under binders
  , locals    :: Locals                -- getting types of fresh metas
  , pruning   :: Pruning               -- getting terms of fresh metas (mask of bound variables)
  , srcNames  :: M.Map Name (Lvl, VTy) -- only contains info relevant to raw name lookup
  , pos       :: SourcePos
  }

names :: Cxt -> [Name]
names = go . locals where
  go Here              = []
  go (Define ls x _ _) = go ls :> x
  go (Bind ls x _)     = go ls :> x

showVal :: Cxt -> Val -> String
showVal cxt v =
  prettyTm 0 (names cxt) (quote (lvl cxt) v) []

showTm :: Cxt -> Tm -> String
showTm cxt t = prettyTm 0 (names cxt) t []

instance Show Cxt where
  show = show . names

emptyCxt :: SourcePos -> Cxt
emptyCxt = Cxt [] 0 Here [] mempty

-- | Extend Cxt with a bound variable.
bind :: Cxt -> Name -> VTy -> Cxt
bind (Cxt env l ls pr ns pos) x ~a =
  Cxt (env :> VVar l)
      (l + 1)
      (Bind ls x (quote l a))
      (pr :> Just Expl)
      (M.insert x (l, a) ns)
      pos

-- | Insert a new binding. This is used when we insert a new implicit lambda in
--   checking.
newBinder :: Cxt -> Name -> VTy -> Cxt
newBinder (Cxt env l ls pr ns pos) x ~a =
  Cxt (env :> VVar l)
      (l + 1)
      (Bind ls x (quote l a))
      (pr :> Just Expl)
      ns                        -- Unchanged! An inserted binder cannot be accessed from
      pos                       --   source syntax

-- | Extend with a definition. We require both terms and values, for efficiency,
--   because when we elaborate let-definitions, we usually already have terms
--   for the definition and its type.
define :: Cxt -> Name -> Tm -> Val -> Ty -> VTy -> Cxt
define (Cxt env l ls pr ns pos) x ~t ~vt ~a ~va  =
  Cxt (env :> vt)
      (l + 1)
      (Define ls x a t)
      (pr :> Nothing)
      (M.insert x (l, va) ns)
      pos

-- | closeVal : (Γ : Con) → Val (Γ, x : A) B → Closure Γ A B
closeVal :: Cxt -> Val -> Closure
closeVal cxt t = Closure (env cxt) (quote (lvl cxt + 1) t)
