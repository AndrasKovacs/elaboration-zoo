
module Presyntax where

import Common

data Tm
  = Var Name                       -- x
  | Lam Name (Either Name Icit) Tm -- \x. t | \{x}. t | \{x = y}. t
  | App Tm Tm (Either Name Icit)   -- t u  | t {u} | t {x = u}
  | U                              -- U
  | Pi Name Icit Tm Tm             -- (x : A) -> B | {x : A} -> B
  | Let Name Tm Tm Tm              -- let x : A = t; u
  | SrcPos SourcePos Tm            -- source position for error reporting
  | Hole                           -- _
  deriving Show
