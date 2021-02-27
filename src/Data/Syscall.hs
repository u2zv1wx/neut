module Data.Syscall where

-- import Data.Platform
import qualified Data.Text as T

-- Left name-of-interface-function | Right (name-of-syscall, number-of-syscall)
-- the `Left` here is required since direct use of syscall in macOS is deprecated since 10.12, and thus we need to
-- use corresponding interface functions.
type Syscall =
  Either T.Text Integer

data SyscallArgKind
  = SyscallArgImm
  | SyscallArgArray
  | SyscallArgStruct
  deriving (Show, Eq)

data Arg
  = ArgImm
  | ArgArray
  | ArgStruct
  | ArgUnused
  deriving (Show)

-- {-# INLINE nsOS #-}
-- nsOS :: T.Text
-- nsOS =
--   "os."

-- {-# INLINE nsOS #-}
-- nsOS :: T.Text
-- nsOS =
--   "os" <> nsSep

-- (system-call 0 e1 e2 e3) みたいな感じで。 (external-call 0 e1 e2 e3) とかでも。

-- asSyscallMaybe :: OS -> Arch -> T.Text -> Maybe (Syscall, [Arg])
-- asSyscallMaybe os arch name =
--   case (os, arch) of
--     (OSLinux, Arch64)
--       | name == nsOS <> "read" ->
--         return (Right ("read", 0), [ArgUnused, ArgImm, ArgArray, ArgImm])
--       | name == nsOS <> "write" ->
--         return (Right ("write", 1), [ArgUnused, ArgImm, ArgArray, ArgImm])
--       | name == nsOS <> "open" ->
--         return (Right ("open", 2), [ArgUnused, ArgArray, ArgImm, ArgImm])
--       | name == nsOS <> "close" ->
--         return (Right ("close", 3), [ArgImm])
--       | name == nsOS <> "socket" ->
--         return (Right ("socket", 41), [ArgImm, ArgImm, ArgImm])
--       | name == nsOS <> "connect" ->
--         return (Right ("connect", 42), [ArgImm, ArgStruct, ArgImm])
--       | name == nsOS <> "accept" ->
--         return (Right ("accept", 43), [ArgImm, ArgStruct, ArgArray])
--       | name == nsOS <> "bind" ->
--         return (Right ("bind", 49), [ArgImm, ArgStruct, ArgImm])
--       | name == nsOS <> "listen" ->
--         return (Right ("listen", 50), [ArgImm, ArgImm])
--       | name == nsOS <> "fork" ->
--         return (Right ("fork", 57), [])
--       | name == nsOS <> "exit" ->
--         return (Right ("exit", 60), [ArgUnused, ArgImm])
--       | name == nsOS <> "wait4" ->
--         return (Right ("wait4", 61), [ArgImm, ArgArray, ArgImm, ArgStruct])
--       | otherwise ->
--         Nothing
--     (OSLinux, ArchAArch64)
--       | name == nsOS <> "close" ->
--         return (Right ("close", 0x39), [ArgImm])
--       | name == nsOS <> "read" ->
--         return (Right ("read", 0x3f), [ArgUnused, ArgImm, ArgArray, ArgImm])
--       | name == nsOS <> "write" ->
--         return (Right ("write", 0x40), [ArgUnused, ArgImm, ArgArray, ArgImm])
--       | name == nsOS <> "socket" ->
--         return (Right ("socket", 0xC6), [ArgImm, ArgImm, ArgImm])
--       | name == nsOS <> "bind" ->
--         return (Right ("bind", 0xC8), [ArgImm, ArgStruct, ArgImm])
--       | name == nsOS <> "listen" ->
--         return (Right ("listen", 0xC9), [ArgImm, ArgImm])
--       | name == nsOS <> "accept" ->
--         return (Right ("accept", 0xCA), [ArgImm, ArgStruct, ArgArray])
--       | name == nsOS <> "connect" ->
--         return (Right ("connect", 0xCB), [ArgImm, ArgStruct, ArgImm])
--       | name == nsOS <> "exit" ->
--         return (Right ("exit", 0x5D), [ArgUnused, ArgImm])
--       | name == nsOS <> "wait4" ->
--         return (Right ("wait4", 0x104), [ArgImm, ArgArray, ArgImm, ArgStruct])
--       | name == nsOS <> "open" ->
--         return (Right ("open", 0x400), [ArgUnused, ArgArray, ArgImm, ArgImm])
--       | otherwise ->
--         Nothing
--     (OSDarwin, Arch64)
--       | name == nsOS <> "exit" ->
--         return (Left "exit", [ArgUnused, ArgImm]) -- 0x2000001
--       | name == nsOS <> "fork" ->
--         return (Left "fork", []) -- 0x2000002
--       | name == nsOS <> "read" ->
--         return (Left "read", [ArgUnused, ArgImm, ArgArray, ArgImm]) -- 0x2000003
--       | name == nsOS <> "write" ->
--         return (Left "write", [ArgUnused, ArgImm, ArgArray, ArgImm]) -- 0x2000004
--       | name == nsOS <> "open" ->
--         return (Left "open", [ArgUnused, ArgArray, ArgImm, ArgImm]) -- 0x2000005
--       | name == nsOS <> "close" ->
--         return (Left "close", [ArgImm]) -- 0x2000006
--       | name == nsOS <> "wait4" ->
--         return (Left "wait4", [ArgImm, ArgArray, ArgImm, ArgStruct]) -- 0x2000007
--       | name == nsOS <> "accept" ->
--         return (Left "accept", [ArgImm, ArgStruct, ArgArray]) -- 0x2000030
--       | name == nsOS <> "socket" ->
--         return (Left "socket", [ArgImm, ArgImm, ArgImm]) -- 0x2000097
--       | name == nsOS <> "connect" ->
--         return (Left "connect", [ArgImm, ArgStruct, ArgImm]) -- 0x2000098
--       | name == nsOS <> "bind" ->
--         return (Left "bind", [ArgImm, ArgStruct, ArgImm]) -- 0x2000104
--       | name == nsOS <> "listen" ->
--         return (Left "listen", [ArgImm, ArgImm]) -- 0x2000106
--       | otherwise ->
--         Nothing
--     (OSDarwin, ArchAArch64) ->
--       Nothing
