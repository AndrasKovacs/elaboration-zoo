
module Syntax where

import Common

--------------------------------------------------------------------------------

type Ty = Tm

-- | A `Pruning` represents a spine of variables, which contains a subsequence
--   of all variables in scope. A `Just` represents application to a var, a
--   `Nothing` skips over a var.
type Pruning = [Maybe Icit]

-- | A reversed pruning. Used for pruning Pi domains, where we have to iterate
--   inside-out.
newtype RevPruning = RevPruning Pruning

revPruning :: Pruning -> RevPruning
revPruning = RevPruning . reverse

-- | Information about the local binders, used for efficiently creating types for
--   fresh metas.
data Locals
  = Here
  | Define Locals Name ~Ty ~Tm
  | Bind Locals Name ~Ty
  deriving Show

-- | Convert type in context to a closed iterated Pi type.  Note: we need `Tm`
--   and `Ty` in `Locals` in order to make this operation efficient. With this, we
--   can simply move things over from `Locals` without having to rename or quote
--   anything.
closeTy :: Locals -> Ty -> Ty
closeTy mcl b = case mcl of
  Here             -> b
  Bind mcl x a     -> closeTy mcl (Pi x Expl a b)
  Define mcl x a t -> closeTy mcl (Let x a t b)

-- | Convert a term in context to a closed term by wrapping it in lambdas and
--   let-definitions. The type of the result is given by `closeTy`.
closeTm :: Locals -> Tm -> Tm
closeTm mcl t = case mcl of
  Here             -> t
  Bind mcl x a     -> closeTm mcl (Lam x Expl t)
  Define mcl x a u -> closeTm mcl (Let x a u t)

data Tm
  = Var Ix
  | Lam Name Icit Tm
  | App Tm Tm Icit
  | AppPruning Tm Pruning  -- ^ Used for applying an inserted or pruned meta to a mask of the scope.
  | U
  | Pi Name Icit Ty Ty
  | Let Name Ty Tm Tm
  | Meta MetaVar
  | PostponedCheck CheckVar
  deriving Show

-- | Unfold `AppPruning` to an iterated application to vars. This applies a term to all de Bruijn indices
--   which are `Just` in the mask.
appPruning :: Tm -> Pruning -> Tm
appPruning t pr = go 0 pr where
  go x []              = t
  go x (pr :> Just i)  = App (go (x + 1) pr) (Var x) i
  go x (pr :> Nothing) = go (x + 1) pr
