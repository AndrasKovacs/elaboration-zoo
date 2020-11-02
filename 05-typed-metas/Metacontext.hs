
module Metacontext where

import Data.IORef
import System.IO.Unsafe
import qualified Data.IntMap as IM

import Common
import Value

--------------------------------------------------------------------------------

data Link = Link {
    prev  :: Maybe MetaVar
  , order :: Double
  , next  :: Maybe MetaVar}
  deriving Show

data MetaEntry
  -- | Previous meta, order, next meta, solution, type
  = Solved {-# unpack #-} Link Val ~VTy
  -- | Previous meta, order, next meta, type
  | Unsolved {-# unpack #-} Link ~VTy

link :: MetaEntry -> Link
link (Solved l _ _) = l
link (Unsolved l _) = l

nextMetaVar :: IORef MetaVar
nextMetaVar = unsafeDupablePerformIO $ newIORef 0
{-# noinline nextMetaVar #-}

greatestMeta :: IORef (Maybe MetaVar)  -- when I push a new meta, I have to link it to the last element
greatestMeta = unsafeDupablePerformIO $ newIORef Nothing
{-# noinline greatestMeta #-}

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

compareMetas :: MetaVar -> MetaVar -> Ordering
compareMetas m1 m2 = case (lookupMeta m1, lookupMeta m2) of
  (Unsolved l _, Unsolved l' _) -> compare (order l) (order l')
  _                             -> impossible

readLink :: MetaVar -> IO Link
readLink m = do
  mcxt <- readIORef mcxt
  case mcxt IM.! coerce m of
    Unsolved l _ -> pure l
    Solved l _ _ -> pure l

updateLink :: Maybe MetaVar -> (Link -> Link) -> MCxt -> MCxt
updateLink Nothing  _ ms = ms
updateLink (Just m) f ms = IM.update (Just . go) (coerce m) ms
  where go :: MetaEntry -> MetaEntry
        go (Unsolved l va) = Unsolved (f l) va
        go (Solved l t va) = Solved (f l) t va

-- | Create a new unsolved meta as the greatest entry.
pushMeta :: VTy -> IO MetaVar
pushMeta ~va = do
  ms   <- readIORef mcxt
  m    <- readIORef nextMetaVar
  writeIORef nextMetaVar (m + 1)
  mmax <- readIORef greatestMeta
  writeIORef greatestMeta (Just m)
  let wm = fromIntegral $ unMetaVar m
  case mmax of
    Nothing   -> do
      writeIORef mcxt $
        IM.insert (coerce m)
                  (Unsolved (Link Nothing wm Nothing) va)
                  ms
    Just mmax -> do
      writeIORef mcxt $
        updateLink (Just mmax) (\l -> l {next = Just m}) $
        IM.insert (coerce m)
                  (Unsolved (Link (Just mmax) wm Nothing) va) $
                  ms
  pure m

-- | Example strengthening: move γ before α
--   (for example, if I want to solve α with t containg γ
-- | α : A, β : B, γ : C
-- | γ : C, α : A, β : B     (have to check that C does not depend on α, β)

-- | Assuming that m1 < m2, both unsolved, insert m2 just before m1.
strengthenMeta :: MetaVar -> MetaVar -> VTy -> IO ()
strengthenMeta m1 m2 m2ty = do
  ms <- readIORef mcxt
  case (ms IM.! (coerce m1), ms IM.! (coerce m2)) of
    (Unsolved (Link p w n) va, Unsolved (Link p' w' n') va') -> do
      case n' of
        Nothing -> writeIORef greatestMeta p'
        _       -> pure ()

      pw <- maybe (pure (-1)) ((order <$>) . readLink) p
      writeIORef mcxt $
        updateLink p         (\l -> l {next = Just m2}) $
        updateLink (Just m1) (\l -> l {prev = Just m2}) $
        updateLink (Just m2) (\l -> l {prev = p, order = (pw + w)/2, next = Just m1}) $
        updateLink p'        (\l -> l {next = n'}) $
        updateLink n'        (\l -> l {prev = p'}) $
        ms
    _ ->
      impossible

reset :: IO ()
reset = do
  writeIORef nextMetaVar 0
  writeIORef greatestMeta Nothing
  writeIORef mcxt mempty
