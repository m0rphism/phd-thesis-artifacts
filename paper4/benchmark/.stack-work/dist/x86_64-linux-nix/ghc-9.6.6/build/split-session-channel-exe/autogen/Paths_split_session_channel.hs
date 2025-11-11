{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
#if __GLASGOW_HASKELL__ >= 810
{-# OPTIONS_GHC -Wno-prepositive-qualified-module #-}
#endif
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -w #-}
module Paths_split_session_channel (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where


import qualified Control.Exception as Exception
import qualified Data.List as List
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

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir `joinFileName` name)

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath




bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath
bindir     = "/home/m0rphism/Work/phd/papers/law-and-order/bsession/notes/session-instance/artifact-final-v2/artifact/benchmark/.stack-work/install/x86_64-linux-nix/0b1dfe112fdefe1a5a78b7ac05b1a29c662301b31105ce29baeadf9960e5f4f9/9.6.6/bin"
libdir     = "/home/m0rphism/Work/phd/papers/law-and-order/bsession/notes/session-instance/artifact-final-v2/artifact/benchmark/.stack-work/install/x86_64-linux-nix/0b1dfe112fdefe1a5a78b7ac05b1a29c662301b31105ce29baeadf9960e5f4f9/9.6.6/lib/x86_64-linux-ghc-9.6.6/split-session-channel-0.1.0.0-FS1kvhui40S88hG5ApIjbc-split-session-channel-exe"
dynlibdir  = "/home/m0rphism/Work/phd/papers/law-and-order/bsession/notes/session-instance/artifact-final-v2/artifact/benchmark/.stack-work/install/x86_64-linux-nix/0b1dfe112fdefe1a5a78b7ac05b1a29c662301b31105ce29baeadf9960e5f4f9/9.6.6/lib/x86_64-linux-ghc-9.6.6"
datadir    = "/home/m0rphism/Work/phd/papers/law-and-order/bsession/notes/session-instance/artifact-final-v2/artifact/benchmark/.stack-work/install/x86_64-linux-nix/0b1dfe112fdefe1a5a78b7ac05b1a29c662301b31105ce29baeadf9960e5f4f9/9.6.6/share/x86_64-linux-ghc-9.6.6/split-session-channel-0.1.0.0"
libexecdir = "/home/m0rphism/Work/phd/papers/law-and-order/bsession/notes/session-instance/artifact-final-v2/artifact/benchmark/.stack-work/install/x86_64-linux-nix/0b1dfe112fdefe1a5a78b7ac05b1a29c662301b31105ce29baeadf9960e5f4f9/9.6.6/libexec/x86_64-linux-ghc-9.6.6/split-session-channel-0.1.0.0"
sysconfdir = "/home/m0rphism/Work/phd/papers/law-and-order/bsession/notes/session-instance/artifact-final-v2/artifact/benchmark/.stack-work/install/x86_64-linux-nix/0b1dfe112fdefe1a5a78b7ac05b1a29c662301b31105ce29baeadf9960e5f4f9/9.6.6/etc"

getBinDir     = catchIO (getEnv "split_session_channel_bindir")     (\_ -> return bindir)
getLibDir     = catchIO (getEnv "split_session_channel_libdir")     (\_ -> return libdir)
getDynLibDir  = catchIO (getEnv "split_session_channel_dynlibdir")  (\_ -> return dynlibdir)
getDataDir    = catchIO (getEnv "split_session_channel_datadir")    (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "split_session_channel_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "split_session_channel_sysconfdir") (\_ -> return sysconfdir)



joinFileName :: String -> String -> FilePath
joinFileName ""  fname = fname
joinFileName "." fname = fname
joinFileName dir ""    = dir
joinFileName dir fname
  | isPathSeparator (List.last dir) = dir ++ fname
  | otherwise                       = dir ++ pathSeparator : fname

pathSeparator :: Char
pathSeparator = '/'

isPathSeparator :: Char -> Bool
isPathSeparator c = c == '/'
