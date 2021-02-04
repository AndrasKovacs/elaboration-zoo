
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
  | Ex Name (Maybe Tm) Tm          -- ∃ (x : A). B   or ∃ x. B
  | Proj1 Tm                       -- x.1
  | Proj2 Tm                       -- x.2
  | Pair Tm Tm                     -- {t, u}
  deriving Show

unpos :: Tm -> Tm
unpos = \case
  Var x       -> Var x
  Lam x i t   -> Lam x  i (unpos t)
  App t u i   -> App (unpos t) (unpos u) i
  Ex x a b    -> Ex x (unpos <$> a) (unpos b)
  Proj1 t     -> Proj1 (unpos t)
  Proj2 t     -> Proj2 (unpos t)
  Pair t u    -> Pair (unpos t) (unpos u)
  U           -> U
  Pi x i a b  -> Pi x i (unpos a) (unpos b)
  Let x a t u -> Let x (unpos a) (unpos t) (unpos u)
  SrcPos _ t  -> unpos t
  Hole        -> Hole
