
module Metacontext where

import Data.IORef
import System.IO.Unsafe
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS

import qualified Presyntax as P
import Cxt.Type
import Common
import Value
import Syntax

--------------------------------------------------------------------------------

-- The context for checking problems is mostly just a duplication of the code
-- for the plain metacontext. It would be possible to merge them into a single
-- data structure, but that would be somewhat less "well-typed", and would make
-- it less efficient to iterate over only metas or only checking problems.

data CheckEntry
  -- ^ In (Unchecked Γ t A m), we postpone checking t with A in Γ and create m
  --   as a fresh meta, which is a "placedholder" for the eventual checking
  --   result. After we actually perform the checking, we have to unify the
  --   result with the placeholder.
  = Unchecked Cxt P.Tm VTy MetaVar

  -- ^ Result of postponed checking. We unfold these when pretty printing terms.
  | Checked Tm

type CCxt = IM.IntMap CheckEntry

type CheckCxt = IM.IntMap CheckEntry

checkCxt :: IORef CheckCxt
checkCxt = unsafeDupablePerformIO $ newIORef mempty
{-# noinline checkCxt #-}

nextCheckVar :: IORef CheckVar
nextCheckVar = unsafeDupablePerformIO $ newIORef 0
{-# noinline nextCheckVar #-}

alterCheck :: CheckVar -> (Maybe CheckEntry -> Maybe CheckEntry) -> IO ()
alterCheck m f = modifyIORef' checkCxt (IM.alter f (coerce m))

modifyCheck :: CheckVar -> (CheckEntry -> CheckEntry) -> IO ()
modifyCheck m f = alterCheck m (maybe (error "impossible") (Just . f))

writeCheck :: CheckVar -> CheckEntry -> IO ()
writeCheck m e = modifyCheck m (const e)

newCheck :: Cxt -> P.Tm -> VTy -> MetaVar -> IO CheckVar
newCheck cxt t a m = do
  c <- readIORef nextCheckVar
  writeIORef nextCheckVar $! c + 1
  alterCheck c (maybe (Just (Unchecked cxt t a m)) impossible)
  pure c

readCheck :: CheckVar -> IO CheckEntry
readCheck c = do
  cs <- readIORef checkCxt
  case IM.lookup (coerce c) cs of
    Just e  -> pure e
    Nothing -> impossible

lookupCheck :: CheckVar -> CheckEntry
lookupCheck = unsafeDupablePerformIO . readCheck

addBlocking :: CheckVar -> MetaVar -> IO ()
addBlocking blocked blocks =
  modifyMeta blocks $ \case
    Unsolved bs a -> Unsolved (IS.insert (coerce blocked) bs) a
    _             -> impossible

--------------------------------------------------------------------------------

-- | Set of checking problems.
type Blocking = IS.IntSet

data MetaEntry
  -- ^ Unsolved meta which may block checking problems.
  = Unsolved Blocking ~VTy

  -- ^ Contains value and type of solution.
  | Solved Val ~VTy

nextMetaVar :: IORef MetaVar
nextMetaVar = unsafeDupablePerformIO $ newIORef 0
{-# noinline nextMetaVar #-}

alterMeta :: MetaVar -> (Maybe MetaEntry -> Maybe MetaEntry) -> IO ()
alterMeta m f = modifyIORef' mcxt (IM.alter f (coerce m))

modifyMeta :: MetaVar -> (MetaEntry -> MetaEntry) -> IO ()
modifyMeta m f = alterMeta m (maybe (error "impossible") (Just . f))

writeMeta :: MetaVar -> MetaEntry -> IO ()
writeMeta m e = modifyMeta m (const e)

newRawMeta :: Blocking -> VTy -> IO MetaVar
newRawMeta bs ~a = do
  m <- readIORef nextMetaVar
  writeIORef nextMetaVar $! m + 1
  alterMeta m (maybe (Just (Unsolved bs a)) impossible)
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

--------------------------------------------------------------------------------

-- | Reset all mutable refs to initial state.
reset :: IO ()
reset = do
  writeIORef nextMetaVar 0
  writeIORef mcxt mempty
  writeIORef nextCheckVar 0
  writeIORef checkCxt mempty
