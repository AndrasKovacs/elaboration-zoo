
module Cxt where

import Common
import Evaluation
import Pretty
import Syntax
import Value

-- Elaboration context
--------------------------------------------------------------------------------

data NameOrigin = Inserted | Source deriving Eq
type Types = [(String, NameOrigin, VTy)]

data Cxt = Cxt {           -- used for:
                           -----------------------------------
    env   :: Env           -- evaluation
  , lvl   :: Lvl           -- unification
  , types :: Types         -- raw name lookup, pretty printing
  , bds   :: [BD]          -- fresh meta creation
  , pos   :: SourcePos     -- error reporting
  }

cxtNames :: Cxt -> [Name]
cxtNames = fmap (\(x, _, _) -> x) . types

showVal :: Cxt -> Val -> String
showVal cxt v =
  prettyTm 0 (cxtNames cxt) (quote (lvl cxt) v) []

showTm :: Cxt -> Tm -> String
showTm cxt t = prettyTm 0 (cxtNames cxt) t []

instance Show Cxt where
  show = show . cxtNames

emptyCxt :: SourcePos -> Cxt
emptyCxt = Cxt [] 0 [] []

-- | Extend Cxt with a bound variable.
bind :: Cxt -> Name -> VTy -> Cxt
bind (Cxt env l types bds pos) x ~a =
  Cxt (env :> VVar l) (l + 1) (types :> (x, Source, a)) (bds :> Bound) pos

-- | Insert a new binding.
newBinder :: Cxt -> Name -> VTy -> Cxt
newBinder (Cxt env l types bds pos) x ~a =
  Cxt (env :> VVar l) (l + 1) (types :> (x, Inserted, a)) (bds :> Bound) pos

-- | Extend Cxt with a definition.
define :: Cxt -> Name -> Val -> VTy -> Cxt
define (Cxt env l types bds pos) x ~t ~a  =
  Cxt (env :> t) (l + 1) (types :> (x, Source, a)) (bds :> Defined) pos

-- | closeVal : (Γ : Con) → Val (Γ, x : A) B → Closure Γ A B
closeVal :: Cxt -> Val -> Closure
closeVal cxt t = Closure (env cxt) (quote (lvl cxt + 1) t)
