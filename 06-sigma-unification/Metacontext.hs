
module Metacontext where

{-|
The metacontext is now dependency-ordered, and we have more stuff to represent
and maintain the ordering. We use a simple "order-maintenance structure", where
entries are ordered by `Double` weights.
-}

import Data.List
import Data.Ord
import Data.IORef
import System.IO.Unsafe
import qualified Data.IntMap as IM

import Common
import Value

--------------------------------------------------------------------------------

-- | Meta entries form a dependency-sorted doubly linked list. Each entry contains a `Double`
--   ordering weight, by which the list is ordered. By having a `Double` stand for the ordering,
--   we can compare metavariable in constant time by comparing the weights. However, we have to
--   maintain weights when we modify the metacontext.
--
--   The previous and next metas can be `Nothing`, to represent when an entry is
--   the first/last in the context.
data Link = Link {
    prev   :: Maybe MetaVar
  , weight :: Double
  , next   :: Maybe MetaVar}
  deriving Show

data MetaEntry
  = Solved {-# unpack #-} Link Val ~VTy -- ^ Link, solution, type.
  | Unsolved {-# unpack #-} Link ~VTy   -- ^ Link, type.

link :: MetaEntry -> Link
link (Solved l _ _) = l
link (Unsolved l _) = l

modifyLink :: (Link -> Link) -> MetaEntry -> MetaEntry
modifyLink f (Solved l t a) = Solved (f l) t a
modifyLink f (Unsolved l a) = Unsolved (f l) a

nextMetaVar :: IORef MetaVar
nextMetaVar = unsafeDupablePerformIO $ newIORef 0
{-# noinline nextMetaVar #-}

-- | A fresh meta is always the last in the context, in dependency-order. We
--   have to keep track of the last (greatest) meta, so that we can link a fresh
--   meta to it.
greatestMeta :: IORef (Maybe MetaVar)
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

lookupUnsolved :: MetaVar -> IO (Link, VTy)
lookupUnsolved m = readMeta m >>= \case
  Unsolved l a -> pure (l, a)
  _            -> impossible

-- It is sensible to compare solved metas as well, but in unification we only need comparison
-- for unsolved metas, so we throw error as a sanity check otherwise.
compareMetas :: MetaVar -> MetaVar -> Ordering
compareMetas m1 m2 = case (lookupMeta m1, lookupMeta m2) of
  (Unsolved l _, Unsolved l' _) -> compare (weight l) (weight l')
  _                             -> impossible

readLink :: MetaVar -> IO Link
readLink m = do
  mcxt <- readIORef mcxt
  case mcxt IM.! coerce m of
    Unsolved l _ -> pure l
    Solved l _ _ -> pure l

-- | Modify the link of a `Maybe MetaVar` with a function.
updateLink :: Maybe MetaVar -> (Link -> Link) -> MCxt -> MCxt
updateLink Nothing  _ ms = ms
updateLink (Just m) f ms = IM.update (Just . modifyLink f) (coerce m) ms

-- | Create a new unsolved meta as the greatest entry.
pushMeta :: VTy -> IO MetaVar
pushMeta ~va = do
  ms   <- readIORef mcxt
  m    <- readIORef nextMetaVar
  writeIORef nextMetaVar (m + 1)
  mmax <- readIORef greatestMeta         -- current greatest meta
  writeIORef greatestMeta (Just m)       -- new greatest meta
  let wm = fromIntegral $ unMetaVar m    -- new greatest meta weight comes from `nextMetaVar`
  case mmax of
    Nothing   -> do     -- metacontext is empty, insert new meta
      writeIORef mcxt $
        IM.insert (coerce m)
                  (Unsolved (Link Nothing wm Nothing) va)
                  ms
    Just mmax -> do    -- metacontext is non-empty, insert new meta and link it to previous greatest meta
      writeIORef mcxt $
        updateLink (Just mmax) (\l -> l {next = Just m}) $
        IM.insert (coerce m)
                  (Unsolved (Link (Just mmax) wm Nothing) va) $
                  ms
  pure m


-- | Assuming that m1 < m2, both unsolved, and m2 : a, `strengthenMeta m1 m2 a`
--   moves m2 to just before m1 in the context. This is used when solving m1 with
--   a value containing m2, because m1's definition can only refer to other metas
--   in m1's scope.
strengthenMeta :: MetaVar -> MetaVar -> VTy -> IO ()
strengthenMeta m1 m2 m2ty = do
  ms <- readIORef mcxt
  case (ms IM.! (coerce m1), ms IM.! (coerce m2)) of
    (Unsolved (Link p w n) va, Unsolved (Link p' w' n') va') -> do

      -- if m2 is the current greatest meta, the next greatest is p'
      case n' of
        Nothing -> writeIORef greatestMeta p'
        _       -> pure ()

      -- We pick a weight which will be smaller than m2's new weight.
      -- If m1 is the least meta, we pick -1, which is smaller than any weight.
      -- Otherwise we pick p's weight.
      pw <- maybe (pure (-1)) ((weight <$>) . readLink) p

      let neww = (pw + w) / 2
      if pw < neww && neww < w then

        -- we update all links. m2's new weight is the average of pw and m1's weight.
        writeIORef mcxt $
          updateLink p         (\l -> l {next = Just m2}) $
          updateLink (Just m1) (\l -> l {prev = Just m2}) $
          updateLink (Just m2) (\l -> l {prev = p, weight = (pw + w)/2, next = Just m1}) $
          updateLink p'        (\l -> l {next = n'}) $
          updateLink n'        (\l -> l {prev = p'}) $
          ms

      -- we've run out of Double precision, so we reassign all weights in increasing order,
      -- then retry strengthening
      else do
        reassignWeights
        strengthenMeta m1 m2 m2ty
    _ ->
      impossible

-- | Reassign all weights in 1-s increments.
reassignWeights :: IO ()
reassignWeights = modifyIORef mcxt $ \ms ->
  IM.fromList $ do
    ((m, e), w) <- zip (sortBy (comparing (weight . link . snd)) (IM.assocs ms))
                       [(0::Double)..]
    pure $ (m, modifyLink (\l -> l {weight = w}) e)

-- | Reset all mutable refs to initial state.
reset :: IO ()
reset = do
  writeIORef nextMetaVar 0
  writeIORef greatestMeta Nothing
  writeIORef mcxt mempty
