
module Syntax where

import Common

type Ty = Tm

type Pruning = [Maybe Icit]  -- spine of some variables in the context
                             -- Nothing skips over some variable in context

-- | A reversed pruning. Used for pruning Pi domains, where we have to iterate
--   inside-out.
newtype RevPruning = RevPruning Pruning

revPruning :: Pruning -> RevPruning
revPruning = RevPruning . reverse

data Path
  = Here
  | Define Path Name ~Ty ~Tm   -- point: Path does not store Val-s!
  | Bind Path Name ~Ty
  deriving Show

data Tm
  = Var Ix
  | Lam Name Icit Tm
  | App Tm Tm Icit
  | AppPruning Tm Pruning   -- Instead: InsertedMeta MetaVar [BD] (any Tm can be applied to a pruning)
  | U
  | Pi Name Icit Ty Ty
  | Let Name Ty Tm Tm
  | Meta MetaVar
  deriving Show

-- x, y, z ⊢ f [Just Expl, Just Impl, Nothing]
