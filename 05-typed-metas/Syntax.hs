
module Syntax where

import Common

type Ty = Tm

data MetaClosure
  = Nil
  | Define MetaClosure Name ~Ty ~Tm
  | Bind MetaClosure Name ~Ty
  deriving Show

data Tm
  = Var Ix
  | Lam Name Icit Tm
  | App Tm Tm Icit
  | U
  | Pi Name Icit Ty Ty
  | Let Name Ty Tm Tm
  | Meta MetaVar
  | InsertedMeta MetaVar MetaClosure
  deriving Show
