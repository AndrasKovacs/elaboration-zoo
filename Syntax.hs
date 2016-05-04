
module Syntax (RawTerm(..)) where

import Data.String

data RawTerm
  = Var !String
  | Lam !String !RawTerm !RawTerm
  | ILam !String !RawTerm          -- implicit arg type
  | Pi  !String !RawTerm !RawTerm  -- explicit arg type
  | App !RawTerm !RawTerm
  | Con !String [RawTerm]
  | Arr !RawTerm !RawTerm
  | Ann !RawTerm !RawTerm
  | Star
  deriving Show

instance IsString RawTerm where
  fromString = Var
