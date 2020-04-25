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
      | name == nsOS <> "read" ->
        return (Right ("read", 0), [ArgUnused, ArgImm, ArgArray, ArgImm])
      | name == nsOS <> "write" ->
        return (Right ("write", 1), [ArgUnused, ArgImm, ArgArray, ArgImm])
      | name == nsOS <> "open" ->
        return (Right ("open", 2), [ArgUnused, ArgArray, ArgImm, ArgImm])
      | name == nsOS <> "close" ->
        return (Right ("close", 3), [ArgImm])
      | name == nsOS <> "socket" ->
        return (Right ("socket", 41), [ArgImm, ArgImm, ArgImm])
      | name == nsOS <> "connect" ->
        return (Right ("connect", 42), [ArgImm, ArgStruct, ArgImm])
      | name == nsOS <> "accept" ->
        return (Right ("accept", 43), [ArgImm, ArgStruct, ArgArray])
      | name == nsOS <> "bind" ->
        return (Right ("bind", 49), [ArgImm, ArgStruct, ArgImm])
      | name == nsOS <> "listen" ->
        return (Right ("listen", 50), [ArgImm, ArgImm])
      | name == nsOS <> "fork" ->
        return (Right ("fork", 57), [])
      | name == nsOS <> "exit" ->
        return (Right ("exit", 60), [ArgUnused, ArgImm])
      | name == nsOS <> "wait4" ->
        return (Right ("wait4", 61), [ArgImm, ArgArray, ArgImm, ArgStruct])
      | otherwise ->
        Nothing
    OSDarwin
      | name == nsOS <> "exit" ->
        return (Left "exit", [ArgUnused, ArgImm]) -- 0x2000001
      | name == nsOS <> "fork" ->
        return (Left "fork", []) -- 0x2000002
      | name == nsOS <> "read" ->
        return (Left "read", [ArgUnused, ArgImm, ArgArray, ArgImm]) -- 0x2000003
      | name == nsOS <> "write" ->
        return (Left "write", [ArgUnused, ArgImm, ArgArray, ArgImm]) -- 0x2000004
      | name == nsOS <> "open" ->
        return (Left "open", [ArgUnused, ArgArray, ArgImm, ArgImm]) -- 0x2000005
      | name == nsOS <> "close" ->
        return (Left "close", [ArgImm]) -- 0x2000006
      | name == nsOS <> "wait4" ->
        return (Left "wait4", [ArgImm, ArgArray, ArgImm, ArgStruct]) -- 0x2000007
      | name == nsOS <> "accept" ->
        return (Left "accept", [ArgImm, ArgStruct, ArgArray]) -- 0x2000030
      | name == nsOS <> "socket" ->
        return (Left "socket", [ArgImm, ArgImm, ArgImm]) -- 0x2000097
      | name == nsOS <> "connect" ->
        return (Left "connect", [ArgImm, ArgStruct, ArgImm]) -- 0x2000098
      | name == nsOS <> "bind" ->
        return (Left "bind", [ArgImm, ArgStruct, ArgImm]) -- 0x2000104
      | name == nsOS <> "listen" ->
        return (Left "listen", [ArgImm, ArgImm]) -- 0x2000106
      | otherwise ->
        Nothing
