
module Common (
    module Common
  , SourcePos(..)
  , Pos
  , unPos
  , module Debug.Trace
  , module Data.Coerce
  , initialPos) where

import Text.Megaparsec
import GHC.Stack
import Debug.Trace
import Data.Coerce

type Dbg = HasCallStack

impossible :: Dbg => a
impossible = error "impossible"

type Name = String

data Icit = Impl | Expl deriving (Eq)

icit :: Icit -> a -> a -> a
icit Impl a _ = a
icit Expl _ b = b

instance Show Icit where
  show Impl = "implicit"
  show Expl = "explicit"

-- | De Bruijn index.
newtype Ix  = Ix {unIx :: Int} deriving (Eq, Show, Num) via Int

-- | De Bruijn level.
newtype Lvl = Lvl {unLvl :: Int} deriving (Eq, Ord, Show, Num) via Int

newtype MetaVar = MetaVar {unMetaVar :: Int} deriving (Eq, Show, Num) via Int


-- Snoc lists
--------------------------------------------------------------------------------

infixl 4 :>

pattern (:>) :: [a] -> a -> [a]
pattern xs :> x <- x:xs where (:>) xs ~x = x:xs
{-# complete (:>), [] #-}
