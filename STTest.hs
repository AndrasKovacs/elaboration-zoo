

import Control.Monad
import Control.Monad.ST
import Data.STRef
import Data.IORef
import System.IO.Unsafe
import Control.Monad.Fix

-- question: can we lazily compute a value from an ST ref/array, so
-- that we first read the ST state when the value is forced, not when
-- the thunk is created?

-- test :: ST s Int
-- test = do
--   ref <- newSTRef (0 :: Int)
--   foo <- (+100) <$> readSTRef ref
--   modifySTRef ref (+100)
--   pure foo

-- main = print $ runST test

test :: ST s [Int]
test = fixST $ \xs -> pure (0 : xs)



-- EXCELLENT!
main :: IO ()
main = do
  ref <- newIORef (0 :: Int)
  let foo = unsafeDupablePerformIO $ (+100) <$> readIORef ref
  modifyIORef' ref (+100)
  print foo





