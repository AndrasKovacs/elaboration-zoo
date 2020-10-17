
module Metacontext where

import Data.IORef
import System.IO.Unsafe

import qualified Data.IntMap as IM

import Common
import Value

--------------------------------------------------------------------------------

data MetaEntry = Solved Val | Unsolved

nextMeta :: IORef Int
nextMeta = unsafeDupablePerformIO $ newIORef 0
{-# noinline nextMeta #-}

mcxt :: IORef (IM.IntMap MetaEntry)
mcxt = unsafeDupablePerformIO $ newIORef mempty
{-# noinline mcxt #-}

lookupMeta :: MetaVar -> MetaEntry
lookupMeta (MetaVar m) = unsafeDupablePerformIO $ do
  ms <- readIORef mcxt
  case IM.lookup m ms of
    Just e  -> pure e
    Nothing -> error "impossible"

reset :: IO ()
reset = do
  writeIORef nextMeta 0
  writeIORef mcxt mempty
