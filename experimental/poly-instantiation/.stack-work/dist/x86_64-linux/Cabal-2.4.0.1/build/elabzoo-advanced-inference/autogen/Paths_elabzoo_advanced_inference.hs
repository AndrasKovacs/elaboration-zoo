{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_elabzoo_advanced_inference (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/home/kutta/Dropbox/src/haskell/elaboration-zoo/.stack-work/install/x86_64-linux/affb10c9e6008994458bb9ceb68ef05864d05e55e54bee21c82d4d3664aa7676/8.6.4/bin"
libdir     = "/home/kutta/Dropbox/src/haskell/elaboration-zoo/.stack-work/install/x86_64-linux/affb10c9e6008994458bb9ceb68ef05864d05e55e54bee21c82d4d3664aa7676/8.6.4/lib/x86_64-linux-ghc-8.6.4/elabzoo-advanced-inference-0.1.0.0-DQ1a8JqUYUpAUW1bpDzye8-elabzoo-advanced-inference"
dynlibdir  = "/home/kutta/Dropbox/src/haskell/elaboration-zoo/.stack-work/install/x86_64-linux/affb10c9e6008994458bb9ceb68ef05864d05e55e54bee21c82d4d3664aa7676/8.6.4/lib/x86_64-linux-ghc-8.6.4"
datadir    = "/home/kutta/Dropbox/src/haskell/elaboration-zoo/.stack-work/install/x86_64-linux/affb10c9e6008994458bb9ceb68ef05864d05e55e54bee21c82d4d3664aa7676/8.6.4/share/x86_64-linux-ghc-8.6.4/elabzoo-advanced-inference-0.1.0.0"
libexecdir = "/home/kutta/Dropbox/src/haskell/elaboration-zoo/.stack-work/install/x86_64-linux/affb10c9e6008994458bb9ceb68ef05864d05e55e54bee21c82d4d3664aa7676/8.6.4/libexec/x86_64-linux-ghc-8.6.4/elabzoo-advanced-inference-0.1.0.0"
sysconfdir = "/home/kutta/Dropbox/src/haskell/elaboration-zoo/.stack-work/install/x86_64-linux/affb10c9e6008994458bb9ceb68ef05864d05e55e54bee21c82d4d3664aa7676/8.6.4/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "elabzoo_advanced_inference_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "elabzoo_advanced_inference_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "elabzoo_advanced_inference_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "elabzoo_advanced_inference_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "elabzoo_advanced_inference_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "elabzoo_advanced_inference_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
