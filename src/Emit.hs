module Emit
  ( emit,
  )
where

import Control.Monad
import Data.Basic
import Data.ByteString.Builder
import Data.Global
import qualified Data.HashMap.Lazy as HashMap
import Data.IORef
import qualified Data.IntMap as IntMap
import Data.Log
import Data.LowComp
import Data.LowType
import qualified Data.Map as Map
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Numeric.Half
import Reduce.LowComp
import qualified System.Info as System

emit :: LowComp -> IO Builder
emit mainTerm = do
  g <- emitDeclarations
  mainTerm' <- reduceLowComp IntMap.empty Map.empty mainTerm
  zs <- emitDefinition "i64" "main" [] mainTerm'
  lenv <- readIORef lowDefEnv
  xs <-
    forM (HashMap.toList lenv) $ \(name, (args, body)) -> do
      let args' = map (showLowValue . LowValueVarLocal) args
      body' <- reduceLowComp IntMap.empty Map.empty body
      emitDefinition "i8*" (TE.encodeUtf8Builder name) args' body'
  return $ unlinesL $ g : zs <> concat xs

emitDeclarations :: IO Builder
emitDeclarations = do
  denv <- HashMap.toList <$> readIORef declEnv
  return $ unlinesL $ map declToBuilder denv

declToBuilder :: (T.Text, ([LowType], LowType)) -> Builder
declToBuilder (name, (dom, cod)) = do
  let name' = TE.encodeUtf8Builder name
  "declare fastcc "
    <> showLowType cod
    <> " @"
    <> name'
    <> "("
    <> showItems showLowType dom
    <> ")"

emitDefinition :: Builder -> Builder -> [Builder] -> LowComp -> IO [Builder]
emitDefinition retType name args asm = do
  let header = sig retType name args <> " {"
  content <- emitLowComp retType asm
  let footer = "}"
  return $ [header] <> content <> [footer]

sig :: Builder -> Builder -> [Builder] -> Builder
sig retType name args =
  "define fastcc " <> retType <> " @" <> name <> showLocals args

emitBlock :: Builder -> Ident -> LowComp -> IO [Builder]
emitBlock funName (I (_, i)) asm = do
  a <- emitLowComp funName asm
  return $ emitLabel ("_" <> intDec i) : a

emitLowComp :: Builder -> LowComp -> IO [Builder]
emitLowComp retType llvm =
  case llvm of
    LowCompReturn d ->
      emitRet retType d
    LowCompCall f args -> do
      tmp <- newIdentFromText "tmp"
      op <-
        emitOp $
          unwordsL
            [ showLowValue (LowValueVarLocal tmp),
              "=",
              "tail call fastcc i8*",
              showLowValue f <> showArgs args
            ]
      a <- emitRet retType (LowValueVarLocal tmp)
      return $ op <> a
    LowCompSwitch (d, lowType) defaultBranch branchList -> do
      defaultLabel <- newIdentFromText "default"
      labelList <- constructLabelList branchList
      op <-
        emitOp $
          unwordsL
            [ "switch",
              showLowType lowType,
              showLowValue d <> ",",
              "label",
              showLowValue (LowValueVarLocal defaultLabel),
              showBranchList lowType $ zip (map fst branchList) labelList
            ]
      let asmList = map snd branchList
      xs <-
        forM (zip labelList asmList <> [(defaultLabel, defaultBranch)]) $
          uncurry (emitBlock retType)
      return $ op <> concat xs
    LowCompCont op cont -> do
      s <- emitLowOp op
      str <- emitOp s
      a <- emitLowComp retType cont
      return $ str <> a
    LowCompLet x op cont -> do
      s <- emitLowOp op
      str <- emitOp $ showLowValue (LowValueVarLocal x) <> " = " <> s
      a <- emitLowComp retType cont
      return $ str <> a
    LowCompUnreachable ->
      emitOp $ unwordsL ["unreachable"]

emitLowOp :: LowOp -> IO Builder
emitLowOp llvmOp =
  case llvmOp of
    LowOpCall d ds ->
      return $ unwordsL ["call fastcc i8*", showLowValue d <> showArgs ds]
    LowOpGetElementPtr (base, n) is ->
      return $
        unwordsL
          [ "getelementptr",
            showLowTypeAsIfNonPtr n <> ",",
            showLowType n,
            showLowValue base <> ",",
            showIndex is
          ]
    LowOpBitcast d fromType toType ->
      emitConvOp "bitcast" d fromType toType
    LowOpIntToPointer d fromType toType ->
      emitConvOp "inttoptr" d fromType toType
    LowOpPointerToInt d fromType toType ->
      emitConvOp "ptrtoint" d fromType toType
    LowOpLoad d lowType ->
      return $
        unwordsL
          [ "load",
            showLowType lowType <> ",",
            showLowTypeAsIfPtr lowType,
            showLowValue d
          ]
    LowOpStore t d1 d2 ->
      return $
        unwordsL
          [ "store",
            showLowType t,
            showLowValue d1 <> ",",
            showLowTypeAsIfPtr t,
            showLowValue d2
          ]
    LowOpAlloc d _ ->
      return $ unwordsL ["call fastcc", "i8*", "@malloc(i8* " <> showLowValue d <> ")"]
    LowOpFree d _ j -> do
      nenv <- readIORef nopFreeSet
      if S.member j nenv
        then return "bitcast i8* null to i8*" -- nop
        else return $ unwordsL ["call fastcc", "i8*", "@free(i8* " <> showLowValue d <> ")"]
    LowOpSyscall num ds ->
      emitSyscallOp num ds
    LowOpPrimOp (PrimOp op domList cod) args -> do
      let op' = TE.encodeUtf8Builder op
      case (S.member op unaryOpSet, S.member op convOpSet, S.member op binaryOpSet, S.member op cmpOpSet) of
        (True, _, _, _) ->
          emitUnaryOp (domList !! 0) op' (args !! 0)
        (_, True, _, _) ->
          emitConvOp op' (args !! 0) (domList !! 0) cod
        (_, _, True, _) ->
          emitBinaryOp (domList !! 0) op' (args !! 0) (args !! 1)
        (_, _, _, True) ->
          emitBinaryOp (domList !! 0) op' (args !! 0) (args !! 1)
        _ ->
          raiseCritical' $ "unknown primitive: " <> op

emitUnaryOp :: LowType -> Builder -> LowValue -> IO Builder
emitUnaryOp t inst d =
  return $ unwordsL [inst, showLowType t, showLowValue d]

emitBinaryOp :: LowType -> Builder -> LowValue -> LowValue -> IO Builder
emitBinaryOp t inst d1 d2 =
  return $
    unwordsL [inst, showLowType t, showLowValue d1 <> ",", showLowValue d2]

emitConvOp :: Builder -> LowValue -> LowType -> LowType -> IO Builder
emitConvOp cast d dom cod =
  return $
    unwordsL [cast, showLowType dom, showLowValue d, "to", showLowType cod]

emitSyscallOp :: Integer -> [LowValue] -> IO Builder
emitSyscallOp num ds = do
  regList <- getRegList
  case System.arch of
    "x86_64" -> do
      let args = (LowValueInt num, LowTypeInt 64) : zip ds (repeat voidPtr)
      let argStr = "(" <> showIndex args <> ")"
      let regStr = "\"=r" <> showRegList (take (length args) regList) <> "\""
      return $
        unwordsL ["call fastcc i8* asm sideeffect \"syscall\",", regStr, argStr]
    "aarch64" -> do
      let args = (LowValueInt num, LowTypeInt 64) : zip ds (repeat voidPtr)
      let argStr = "(" <> showIndex args <> ")"
      let regStr = "\"=r" <> showRegList (take (length args) regList) <> "\""
      return $
        unwordsL ["call fastcc i8* asm sideeffect \"svc 0\",", regStr, argStr]
    targetArch ->
      raiseCritical' $ "unsupported target arch: " <> T.pack (show targetArch)

emitOp :: Builder -> IO [Builder]
emitOp s =
  return ["  " <> s]

emitRet :: Builder -> LowValue -> IO [Builder]
emitRet retType d =
  emitOp $ unwordsL ["ret", retType, showLowValue d]

emitLabel :: Builder -> Builder
emitLabel s =
  s <> ":"

constructLabelList :: [a] -> IO [Ident]
constructLabelList input =
  case input of
    [] ->
      return []
    (_ : rest) -> do
      label <- newIdentFromText "case"
      labelList <- constructLabelList rest
      return $ label : labelList

showRegList :: [Builder] -> Builder
showRegList regList =
  case regList of
    [] ->
      ""
    (s : ss) ->
      ",{" <> s <> "}" <> showRegList ss

showBranchList :: LowType -> [(Int, Ident)] -> Builder
showBranchList lowType xs =
  "[" <> unwordsL (map (uncurry (showBranch lowType)) xs) <> "]"

showIndex :: [(LowValue, LowType)] -> Builder
showIndex idxList =
  case idxList of
    [] ->
      ""
    [(d, t)] ->
      showLowType t <> " " <> showLowValue d
    ((d, t) : dts) ->
      showIndex [(d, t)] <> ", " <> showIndex dts

showBranch :: LowType -> Int -> Ident -> Builder
showBranch lowType i label =
  showLowType lowType
    <> " "
    <> intDec i
    <> ", label "
    <> showLowValue (LowValueVarLocal label)

showArg :: LowValue -> Builder
showArg d =
  "i8* " <> showLowValue d

showLocal :: Builder -> Builder
showLocal x =
  "i8* " <> x

showArgs :: [LowValue] -> Builder
showArgs ds =
  "(" <> showItems showArg ds <> ")"

showLocals :: [Builder] -> Builder
showLocals ds =
  "(" <> showItems showLocal ds <> ")"

showLowTypeAsIfPtr :: LowType -> Builder
showLowTypeAsIfPtr t =
  showLowType t <> "*"

showLowTypeAsIfNonPtr :: LowType -> Builder
showLowTypeAsIfNonPtr lowType =
  case lowType of
    LowTypeInt i ->
      "i" <> intDec i
    LowTypeFloat FloatSize16 ->
      "half"
    LowTypeFloat FloatSize32 ->
      "float"
    LowTypeFloat FloatSize64 ->
      "double"
    LowTypeStruct ts ->
      "{" <> showItems showLowType ts <> "}"
    LowTypeFunction ts t ->
      showLowType t <> " (" <> showItems showLowType ts <> ")"
    LowTypeArray i t -> do
      let s = showLowType t
      "[" <> intDec i <> " x " <> s <> "]"
    LowTypePointer t ->
      showLowType t

getRegList :: IO [Builder]
getRegList = do
  case (System.os, System.arch) of
    ("linux", "x86_64") ->
      return ["rax", "rdi", "rsi", "rdx", "rcx", "r8", "r9"]
    ("linux", "aarch64") ->
      return ["x8", "x0", "x1", "x2", "x3", "x4", "x5"]
    ("darwin", "x86_64") ->
      return ["rax", "rdi", "rsi", "rdx", "r10", "r8", "r9"]
    (targetOS, targetArch) ->
      raiseError' $ "unsupported target: " <> T.pack targetOS <> " (" <> T.pack targetArch <> ")"

showLowType :: LowType -> Builder
showLowType lowType =
  case lowType of
    LowTypeInt i ->
      "i" <> intDec i
    LowTypeFloat FloatSize16 ->
      "half"
    LowTypeFloat FloatSize32 ->
      "float"
    LowTypeFloat FloatSize64 ->
      "double"
    LowTypeStruct ts ->
      "{" <> showItems showLowType ts <> "}"
    LowTypeFunction ts t ->
      showLowType t <> " (" <> showItems showLowType ts <> ")"
    LowTypeArray i t -> do
      let s = showLowType t
      "[" <> intDec i <> " x " <> s <> "]"
    LowTypePointer t ->
      showLowType t <> "*"

showLowValue :: LowValue -> Builder
showLowValue llvmValue =
  case llvmValue of
    LowValueVarLocal (I (_, i)) ->
      "%_" <> intDec i
    LowValueVarGlobal x ->
      "@" <> TE.encodeUtf8Builder x
    LowValueInt i ->
      integerDec i
    LowValueFloat FloatSize16 x -> do
      let x' = realToFrac x :: Half
      "0x" <> doubleHexFixed (realToFrac x')
    LowValueFloat FloatSize32 x -> do
      let x' = realToFrac x :: Float
      "0x" <> doubleHexFixed (realToFrac x')
    LowValueFloat FloatSize64 x -> do
      let x' = realToFrac x :: Double
      "0x" <> doubleHexFixed (realToFrac x')
    LowValueNull ->
      "null"

showItems :: (a -> Builder) -> [a] -> Builder
showItems f itemList =
  case itemList of
    [] ->
      ""
    [a] ->
      f a
    a : as ->
      f a <> ", " <> showItems f as

{-# INLINE unwordsL #-}
unwordsL :: [Builder] -> Builder
unwordsL strList =
  case strList of
    [] ->
      ""
    [b] ->
      b
    b : bs ->
      b <> " " <> unwordsL bs

{-# INLINE unlinesL #-}
unlinesL :: [Builder] -> Builder
unlinesL strList =
  case strList of
    [] ->
      ""
    [b] ->
      b
    b : bs ->
      b <> "\n" <> unlinesL bs
