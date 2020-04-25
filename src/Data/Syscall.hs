module Data.Syscall where

import Data.Basic
import qualified Data.Text as T

data Arg
  = ArgImm
  | ArgArray
  | ArgStruct
  | ArgUnused
  deriving (Show)

asSysCallMaybe :: OS -> T.Text -> Maybe (Syscall, [Arg])
asSysCallMaybe os name =
  case os of
    OSLinux
      | name == "os" <> nsSep <> "read" ->
        return (Right ("read", 0), [ArgUnused, ArgImm, ArgArray, ArgImm])
      | name == "os" <> nsSep <> "write" ->
        return (Right ("write", 1), [ArgUnused, ArgImm, ArgArray, ArgImm])
      | name == "os" <> nsSep <> "open" ->
        return (Right ("open", 2), [ArgUnused, ArgArray, ArgImm, ArgImm])
      | name == "os" <> nsSep <> "close" ->
        return (Right ("close", 3), [ArgImm])
      | name == "os" <> nsSep <> "socket" ->
        return (Right ("socket", 41), [ArgImm, ArgImm, ArgImm])
      | name == "os" <> nsSep <> "connect" ->
        return (Right ("connect", 42), [ArgImm, ArgStruct, ArgImm])
      | name == "os" <> nsSep <> "accept" ->
        return (Right ("accept", 43), [ArgImm, ArgStruct, ArgArray])
      | name == "os" <> nsSep <> "bind" ->
        return (Right ("bind", 49), [ArgImm, ArgStruct, ArgImm])
      | name == "os" <> nsSep <> "listen" ->
        return (Right ("listen", 50), [ArgImm, ArgImm])
      | name == "os" <> nsSep <> "fork" ->
        return (Right ("fork", 57), [])
      | name == "os" <> nsSep <> "exit" ->
        return (Right ("exit", 60), [ArgUnused, ArgImm])
      | name == "os" <> nsSep <> "wait4" ->
        return (Right ("wait4", 61), [ArgImm, ArgArray, ArgImm, ArgStruct])
      | otherwise ->
        Nothing
    OSDarwin
      | name == "os" <> nsSep <> "exit" ->
        return (Left "exit", [ArgUnused, ArgImm]) -- 0x2000001
      | name == "os" <> nsSep <> "fork" ->
        return (Left "fork", []) -- 0x2000002
      | name == "os" <> nsSep <> "read" ->
        return (Left "read", [ArgUnused, ArgImm, ArgArray, ArgImm]) -- 0x2000003
      | name == "os" <> nsSep <> "write" ->
        return (Left "write", [ArgUnused, ArgImm, ArgArray, ArgImm]) -- 0x2000004
      | name == "os" <> nsSep <> "open" ->
        return (Left "open", [ArgUnused, ArgArray, ArgImm, ArgImm]) -- 0x2000005
      | name == "os" <> nsSep <> "close" ->
        return (Left "close", [ArgImm]) -- 0x2000006
      | name == "os" <> nsSep <> "wait4" ->
        return (Left "wait4", [ArgImm, ArgArray, ArgImm, ArgStruct]) -- 0x2000007
      | name == "os" <> nsSep <> "accept" ->
        return (Left "accept", [ArgImm, ArgStruct, ArgArray]) -- 0x2000030
      | name == "os" <> nsSep <> "socket" ->
        return (Left "socket", [ArgImm, ArgImm, ArgImm]) -- 0x2000097
      | name == "os" <> nsSep <> "connect" ->
        return (Left "connect", [ArgImm, ArgStruct, ArgImm]) -- 0x2000098
      | name == "os" <> nsSep <> "bind" ->
        return (Left "bind", [ArgImm, ArgStruct, ArgImm]) -- 0x2000104
      | name == "os" <> nsSep <> "listen" ->
        return (Left "listen", [ArgImm, ArgImm]) -- 0x2000106
      | otherwise ->
        Nothing
