
module Cxt.Type where

import qualified Data.Map as M

import Common
import Syntax
import Value

data Cxt = Cxt {                       -- Used for:
    env       :: Env                   -- evaluation
  , lvl       :: Lvl                   -- going under binders
  , path      :: Path                  -- getting types of fresh metas
  , pruning   :: Pruning               -- getting terms of fresh metas (mask of bound variables)
  , srcNames  :: M.Map Name (Lvl, VTy) -- only contains info relevant to raw name lookup
  , pos       :: SourcePos
  }

names :: Cxt -> [Name]
names = go . path where
  go Here                = []
  go (Define path x _ _) = go path :> x
  go (Bind path x _)     = go path :> x

instance Show Cxt where
  show = show . names
