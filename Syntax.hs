
{-# LANGUAGE RecursiveDo, PatternGuards, OverloadedStrings, LambdaCase #-}

module Syntax (RawTerm(..)) where

import Data.Char
import Data.String

data Token = TStar | TId String | TOpen | TClose | TColon | TDot | TArr
  deriving (Eq, Show)

instance IsString Token where
  fromString = \case
    "*"  -> TStar
    "->" -> TArr
    "("  -> TOpen
    ")"  -> TClose
    ":"  -> TColon
    "."  -> TDot

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
