
module Metacontext where

import Data.IORef
import System.IO.Unsafe
import qualified Data.IntMap as IM

import Common
import Value

--------------------------------------------------------------------------------

data MetaEntry
  = Solved Val ~VTy  -- ^ Solution, type.
  | Unsolved ~VTy    -- ^ Type.

nextMetaVar :: IORef MetaVar
nextMetaVar = unsafeDupablePerformIO $ newIORef 0
{-# noinline nextMetaVar #-}

newMeta :: VTy -> IO MetaVar
newMeta ~a = do
  m <- readIORef nextMetaVar
  writeIORef nextMetaVar $! m + 1
  modifyIORef mcxt $ IM.insert (coerce m) (Unsolved a)
  pure m

type MCxt = IM.IntMap MetaEntry

mcxt :: IORef MCxt
mcxt = unsafeDupablePerformIO $ newIORef mempty
{-# noinline mcxt #-}

readMeta :: MetaVar -> IO MetaEntry
readMeta m = do
  ms <- readIORef mcxt
  case IM.lookup (coerce m) ms of
    Just e  -> pure e
    Nothing -> impossible

lookupMeta :: MetaVar -> MetaEntry
lookupMeta = unsafeDupablePerformIO . readMeta

-- | Reset all mutable refs to initial state.
reset :: IO ()
reset = do
  writeIORef nextMetaVar 0
  writeIORef mcxt mempty
