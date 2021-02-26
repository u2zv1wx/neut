module Data.Platform where

import Control.Exception.Safe
import Data.Log
import qualified Data.Text as T
import System.Info

data OS
  = OSLinux
  | OSDarwin
  deriving (Eq, Show)

showOS :: OS -> T.Text
showOS x =
  case x of
    OSLinux ->
      "linux"
    OSDarwin ->
      "darwin"

data Arch
  = Arch64
  | ArchAArch64
  deriving (Eq, Show)

showArch :: Arch -> T.Text
showArch Arch64 =
  "x64"
showArch ArchAArch64 =
  "aarch64"

getOS :: (MonadThrow m) => m OS
getOS =
  case os of
    "linux" ->
      return OSLinux
    "darwin" ->
      return OSDarwin
    s ->
      raiseCritical' $ "unsupported target os: " <> T.pack (show s)

getArch :: (MonadThrow m) => m Arch
getArch =
  case arch of
    "x86_64" ->
      return Arch64
    "aarch64" ->
      return ArchAArch64
    s ->
      raiseCritical' $ "unsupported target arch: " <> T.pack (show s)
