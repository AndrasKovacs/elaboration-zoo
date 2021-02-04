
module Syntax where

import Common

type Ty = Tm

-- | A `Pruning` represents a spine of variables, which contains a subsequence
--   of all variables in scope. A `Just` represents application to a var, a `Nothing`
--   skips over a var.
type Pruning = [Maybe Icit]

-- | A reversed pruning. Used for pruning Pi domains, where we have to iterate
--   inside-out.
newtype RevPruning = RevPruning Pruning

revPruning :: Pruning -> RevPruning
revPruning = RevPruning . reverse

-- | A "context zipper", used for efficiently creating types for fresh metas.
data Path
  = Here
  | Define Path Name ~Ty ~Tm
  | Bind Path Name ~Ty
  deriving Show

-- | Convert type in context to a closed iterated Pi type.  Note: we need `Tm`
--   and `Ty` in path in order to make this operation efficient. With this, we
--   can simply move things over from `Path` without having to rename or quote
--   anything.
closeTy :: Path -> Ty -> Ty
closeTy mcl b = case mcl of
  Here             -> b
  Bind mcl x a     -> closeTy mcl (Pi x Expl a b)
  Define mcl x a t -> closeTy mcl (Let x a t b)

data Tm
  = Var Ix
  | Lam Name Icit Tm
  | App Tm Tm Icit
  | AppPruning Tm Pruning  -- ^ Used for applying an inserted or pruned meta to a mask of the scope.
  | Ex Name Ty Ty
  | Proj1 Tm
  | Proj2 Tm
  | Pair Tm Tm
  | U
  | Pi Name Icit Ty Ty
  | Let Name Ty Tm Tm
  | Meta MetaVar
  | Postponed MetaVar Tm -- ^ Postponed problem (either checking or subtype coercion), with MetaVar
                         -- identifier and Tm a fresh meta spine standing for the eventual result.
                         -- We have a post-processing "zonking" step which inlines solutions to
                         -- postponings. In principle we could just keep the representing meta instead,
                         -- but that would cause output size increase.

  | Wk Tm                -- ^ Explicit weakening, used in subtyping coercions.
  deriving Show
