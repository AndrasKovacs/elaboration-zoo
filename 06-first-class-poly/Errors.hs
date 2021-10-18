
module Errors where

import Control.Exception
import Text.Printf

import Common
import Cxt
import Syntax

--------------------------------------------------------------------------------

data UnifyException = UnifyException
  deriving (Show, Exception)

data CantUnify
  = ExpectedInferred
  | LamBinderType
  | Placeholder
  deriving Show

data ElabError
  = NameNotInScope Name
  | CantUnify Tm Tm CantUnify
  | InferNamedLam
  | NoNamedImplicitArg Name
  | IcitMismatch Icit Icit
  deriving (Show, Exception)

data Error = Error Cxt ElabError
  deriving (Show, Exception)

displayError :: String -> Error -> IO ()
displayError file (Error cxt e) = do

  let SourcePos path (unPos -> linum) (unPos -> colnum) = pos cxt
      lnum = show linum
      lpad = map (const ' ') lnum
      msg = case e of
        NameNotInScope x ->
          "Name not in scope: " ++ x
        CantUnify t t' ExpectedInferred  ->
          ("Cannot unify expected type\n\n" ++
           "  " ++ showTm cxt t ++ "\n\n" ++
           "with inferred type\n\n" ++
           "  " ++ showTm cxt t')
        CantUnify t t' LamBinderType   ->
          ("Cannot unify expected lambda binder type\n\n" ++
           "  " ++ showTm cxt t ++ "\n\n" ++
           "with given type annotation\n\n" ++
           "  " ++ showTm cxt t')
        CantUnify t t' Placeholder   ->
          ("Cannot unify value\n\n" ++
           "  " ++ showTm cxt t ++ "\n\n" ++
           "with expected value\n\n" ++
           "  " ++ showTm cxt t')
        InferNamedLam ->
          "Cannot infer type for lambda with named argument"
        NoNamedImplicitArg name ->
          "No named implicit argument with name " ++ name
        IcitMismatch i i' -> printf (
          "Function icitness mismatch: expected %s, got %s.")
          (show i) (show i')

  printf "%s:%d:%d:\n" path linum colnum
  printf "%s |\n"    lpad
  printf "%s | %s\n" lnum (lines file !! (linum - 1))
  printf "%s | %s\n" lpad (replicate (colnum - 1) ' ' ++ "^")
  printf "%s\n" msg
