
module Presyntax where

import Common

data Tm
  = Var Name                       -- x
  | Lam Name (Either Name Icit) Tm -- \x. t | \{x}. t | \{x = y}. t
  | App Tm Tm (Either Name Icit)   -- t u  | t {u} | t {x = u}
  | U                              -- U
  | Pi Name Icit Tm Tm             -- (x : A) -> B | {x : A} -> B
  | Let Name Tm Tm Tm              -- let x : A = t; u
  | Sg Name Tm Tm                  -- (x : A) * B
  | Pair Tm Tm                     -- (t, u)
  | Proj1 Tm                       -- t.1
  | Proj2 Tm                       -- t.2
  | ProjField Tm Name              -- t.x
  | Hole                           -- _
  | SrcPos (DontShow SourcePos) Tm -- source position for error reporting
  deriving Show
