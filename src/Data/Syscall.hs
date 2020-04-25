module Data.Syscall where

import Data.Namespace
import Data.Platform
import qualified Data.Text as T

-- Left name-of-interface-function | Right (name-of-syscall, number-of-syscall)
-- the `Left` here is required since direct use of syscall in macOS is deprecated since 10.12, and thus we need to
-- use corresponding interface functions.
type Syscall =
  Either T.Text (T.Text, Integer)

data Arg
  = ArgImm
  | ArgArray
  | ArgStruct
  | ArgUnused
  deriving (Show)

asSyscallMaybe :: OS -> T.Text -> Maybe (Syscall, [Arg])
asSyscallMaybe os name =
  case os of
    OSLinux
      | name == syscallPrefix <> "read" ->
        return (Right ("read", 0), [ArgUnused, ArgImm, ArgArray, ArgImm])
      | name == syscallPrefix <> "write" ->
        return (Right ("write", 1), [ArgUnused, ArgImm, ArgArray, ArgImm])
      | name == syscallPrefix <> "open" ->
        return (Right ("open", 2), [ArgUnused, ArgArray, ArgImm, ArgImm])
      | name == syscallPrefix <> "close" ->
        return (Right ("close", 3), [ArgImm])
      | name == syscallPrefix <> "socket" ->
        return (Right ("socket", 41), [ArgImm, ArgImm, ArgImm])
      | name == syscallPrefix <> "connect" ->
        return (Right ("connect", 42), [ArgImm, ArgStruct, ArgImm])
      | name == syscallPrefix <> "accept" ->
        return (Right ("accept", 43), [ArgImm, ArgStruct, ArgArray])
      | name == syscallPrefix <> "bind" ->
        return (Right ("bind", 49), [ArgImm, ArgStruct, ArgImm])
      | name == syscallPrefix <> "listen" ->
        return (Right ("listen", 50), [ArgImm, ArgImm])
      | name == syscallPrefix <> "fork" ->
        return (Right ("fork", 57), [])
      | name == syscallPrefix <> "exit" ->
        return (Right ("exit", 60), [ArgUnused, ArgImm])
      | name == syscallPrefix <> "wait4" ->
        return (Right ("wait4", 61), [ArgImm, ArgArray, ArgImm, ArgStruct])
      | otherwise ->
        Nothing
    OSDarwin
      | name == syscallPrefix <> "exit" ->
        return (Left "exit", [ArgUnused, ArgImm]) -- 0x2000001
      | name == syscallPrefix <> "fork" ->
        return (Left "fork", []) -- 0x2000002
      | name == syscallPrefix <> "read" ->
        return (Left "read", [ArgUnused, ArgImm, ArgArray, ArgImm]) -- 0x2000003
      | name == syscallPrefix <> "write" ->
        return (Left "write", [ArgUnused, ArgImm, ArgArray, ArgImm]) -- 0x2000004
      | name == syscallPrefix <> "open" ->
        return (Left "open", [ArgUnused, ArgArray, ArgImm, ArgImm]) -- 0x2000005
      | name == syscallPrefix <> "close" ->
        return (Left "close", [ArgImm]) -- 0x2000006
      | name == syscallPrefix <> "wait4" ->
        return (Left "wait4", [ArgImm, ArgArray, ArgImm, ArgStruct]) -- 0x2000007
      | name == syscallPrefix <> "accept" ->
        return (Left "accept", [ArgImm, ArgStruct, ArgArray]) -- 0x2000030
      | name == syscallPrefix <> "socket" ->
        return (Left "socket", [ArgImm, ArgImm, ArgImm]) -- 0x2000097
      | name == syscallPrefix <> "connect" ->
        return (Left "connect", [ArgImm, ArgStruct, ArgImm]) -- 0x2000098
      | name == syscallPrefix <> "bind" ->
        return (Left "bind", [ArgImm, ArgStruct, ArgImm]) -- 0x2000104
      | name == syscallPrefix <> "listen" ->
        return (Left "listen", [ArgImm, ArgImm]) -- 0x2000106
      | otherwise ->
        Nothing

{-# INLINE syscallPrefix #-}
syscallPrefix :: T.Text
syscallPrefix =
  "os" <> nsSep
