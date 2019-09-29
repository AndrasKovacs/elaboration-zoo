{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_elabzoo_poly_instantiation (
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

bindir     = "/home/kutta/home/Dropbox/src/haskell/elaboration-zoo/.stack-work/install/x86_64-linux/fca9db4443c9dd5a9f651a5e89702de9ef59b4d01693ce80fea0c5f0990c940d/8.6.4/bin"
libdir     = "/home/kutta/home/Dropbox/src/haskell/elaboration-zoo/.stack-work/install/x86_64-linux/fca9db4443c9dd5a9f651a5e89702de9ef59b4d01693ce80fea0c5f0990c940d/8.6.4/lib/x86_64-linux-ghc-8.6.4/elabzoo-poly-instantiation-0.1.0.0-2M3tXtTOMyJK1YvNoiFC4e-elabzoo-poly-instantiation"
dynlibdir  = "/home/kutta/home/Dropbox/src/haskell/elaboration-zoo/.stack-work/install/x86_64-linux/fca9db4443c9dd5a9f651a5e89702de9ef59b4d01693ce80fea0c5f0990c940d/8.6.4/lib/x86_64-linux-ghc-8.6.4"
datadir    = "/home/kutta/home/Dropbox/src/haskell/elaboration-zoo/.stack-work/install/x86_64-linux/fca9db4443c9dd5a9f651a5e89702de9ef59b4d01693ce80fea0c5f0990c940d/8.6.4/share/x86_64-linux-ghc-8.6.4/elabzoo-poly-instantiation-0.1.0.0"
libexecdir = "/home/kutta/home/Dropbox/src/haskell/elaboration-zoo/.stack-work/install/x86_64-linux/fca9db4443c9dd5a9f651a5e89702de9ef59b4d01693ce80fea0c5f0990c940d/8.6.4/libexec/x86_64-linux-ghc-8.6.4/elabzoo-poly-instantiation-0.1.0.0"
sysconfdir = "/home/kutta/home/Dropbox/src/haskell/elaboration-zoo/.stack-work/install/x86_64-linux/fca9db4443c9dd5a9f651a5e89702de9ef59b4d01693ce80fea0c5f0990c940d/8.6.4/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "elabzoo_poly_instantiation_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "elabzoo_poly_instantiation_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "elabzoo_poly_instantiation_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "elabzoo_poly_instantiation_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "elabzoo_poly_instantiation_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "elabzoo_poly_instantiation_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
