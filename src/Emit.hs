module Emit
  ( emit,
  )
where

import Control.Monad.State.Lazy
import Data.Basic
import Data.ByteString.Builder
import Data.Env
import qualified Data.HashMap.Lazy as HashMap
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

emit :: LowComp -> WithEnv Builder
emit mainTerm = do
  g <- emitDeclarations
  mainTerm' <- reduceLowComp IntMap.empty Map.empty mainTerm
  zs <- emitDefinition "i64" "main" [] mainTerm'
  lenv <- gets lowCompEnv
  xs <-
    forM (HashMap.toList lenv) $ \(name, (args, body)) -> do
      let args' = map (showLowValue . LowValueLocal) args
      body' <- reduceLowComp IntMap.empty Map.empty body
      emitDefinition "i8*" (TE.encodeUtf8Builder name) args' body'
  return $ unlinesL $ g : zs <> concat xs

emitDeclarations :: WithEnv Builder
emitDeclarations = do
  denv <- HashMap.toList <$> gets declEnv
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

emitDefinition :: Builder -> Builder -> [Builder] -> LowComp -> WithEnv [Builder]
emitDefinition retType name args asm = do
  let header = sig retType name args <> " {"
  content <- emitLowComp retType asm
  let footer = "}"
  return $ [header] <> content <> [footer]

sig :: Builder -> Builder -> [Builder] -> Builder
sig retType name args =
  "define fastcc " <> retType <> " @" <> name <> showLocals args

emitBlock :: Builder -> Ident -> LowComp -> WithEnv [Builder]
emitBlock funName (I (_, i)) asm = do
  a <- emitLowComp funName asm
  return $ emitLabel ("_" <> intDec i) : a

emitLowComp :: Builder -> LowComp -> WithEnv [Builder]
emitLowComp retType llvm =
  case llvm of
    LowCompReturn d ->
      emitRet retType d
    LowCompCall f args -> do
      tmp <- newNameWith' "tmp"
      op <-
        emitOp $
          unwordsL
            [ showLowValue (LowValueLocal tmp),
              "=",
              "tail call fastcc i8*",
              showLowValue f <> showArgs args
            ]
      a <- emitRet retType (LowValueLocal tmp)
      return $ op <> a
    LowCompSwitch (d, lowType) defaultBranch branchList -> do
      defaultLabel <- newNameWith' "default"
      labelList <- constructLabelList branchList
      op <-
        emitOp $
          unwordsL
            [ "switch",
              showLowType lowType,
              showLowValue d <> ",",
              "label",
              showLowValue (LowValueLocal defaultLabel),
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
      str <- emitOp $ showLowValue (LowValueLocal x) <> " = " <> s
      a <- emitLowComp retType cont
      return $ str <> a
    LowCompUnreachable ->
      emitOp $ unwordsL ["unreachable"]

emitLowOp :: LowOp -> WithEnv Builder
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
      emitLowCompConvOp "bitcast" d fromType toType
    LowOpIntToPointer d fromType toType ->
      emitLowCompConvOp "inttoptr" d fromType toType
    LowOpPointerToInt d fromType toType ->
      emitLowCompConvOp "ptrtoint" d fromType toType
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
      nenv <- gets nopFreeSet
      if S.member j nenv
        then return "bitcast i8* null to i8*" -- nop
        else return $ unwordsL ["call fastcc", "i8*", "@free(i8* " <> showLowValue d <> ")"]
    LowOpSyscall num ds ->
      emitSyscallOp num ds
    LowOpUnaryOp (UnaryOpFNeg t) d ->
      emitUnaryOp t "fneg" d
    LowOpUnaryOp (UnaryOpTrunc t1 t2) d ->
      emitLowCompConvOp "trunc" d t1 t2
    LowOpUnaryOp (UnaryOpFpTrunc t1 t2) d ->
      emitLowCompConvOp "fptrunc" d t1 t2
    LowOpUnaryOp (UnaryOpZext t1 t2) d ->
      emitLowCompConvOp "zext" d t1 t2
    LowOpUnaryOp (UnaryOpSext t1 t2) d ->
      emitLowCompConvOp "sext" d t1 t2
    LowOpUnaryOp (UnaryOpFpExt t1 t2) d ->
      emitLowCompConvOp "fpext" d t1 t2
    LowOpUnaryOp (UnaryOpUF t1 t2) d ->
      emitLowCompConvOp "uitofp" d t1 t2
    LowOpUnaryOp (UnaryOpSF t1 t2) d ->
      emitLowCompConvOp "sitofp" d t1 t2
    LowOpUnaryOp (UnaryOpFU t1 t2) d ->
      emitLowCompConvOp "fptoui" d t1 t2
    LowOpUnaryOp (UnaryOpFS t1 t2) d ->
      emitLowCompConvOp "fptosi" d t1 t2
    LowOpBinaryOp (BinaryOpAdd t) d1 d2 ->
      emitBinaryOp t "add" d1 d2
    LowOpBinaryOp (BinaryOpFAdd t) d1 d2 ->
      emitBinaryOp t "fadd" d1 d2
    LowOpBinaryOp (BinaryOpSub t) d1 d2 ->
      emitBinaryOp t "sub" d1 d2
    LowOpBinaryOp (BinaryOpFSub t) d1 d2 ->
      emitBinaryOp t "fsub" d1 d2
    LowOpBinaryOp (BinaryOpMul t) d1 d2 ->
      emitBinaryOp t "mul" d1 d2
    LowOpBinaryOp (BinaryOpFMul t) d1 d2 ->
      emitBinaryOp t "fmul" d1 d2
    LowOpBinaryOp (BinaryOpSDiv t) d1 d2 ->
      emitBinaryOp t "sdiv" d1 d2
    LowOpBinaryOp (BinaryOpUDiv t) d1 d2 ->
      emitBinaryOp t "udiv" d1 d2
    LowOpBinaryOp (BinaryOpFDiv t) d1 d2 ->
      emitBinaryOp t "fdiv" d1 d2
    LowOpBinaryOp (BinaryOpSRem t) d1 d2 ->
      emitBinaryOp t "srem" d1 d2
    LowOpBinaryOp (BinaryOpURem t) d1 d2 ->
      emitBinaryOp t "urem" d1 d2
    LowOpBinaryOp (BinaryOpFRem t) d1 d2 ->
      emitBinaryOp t "frem" d1 d2
    LowOpBinaryOp (BinaryOpShl t) d1 d2 ->
      emitBinaryOp t "shl" d1 d2
    LowOpBinaryOp (BinaryOpLshr t) d1 d2 ->
      emitBinaryOp t "lshr" d1 d2
    LowOpBinaryOp (BinaryOpAshr t) d1 d2 ->
      emitBinaryOp t "ashr" d1 d2
    LowOpBinaryOp (BinaryOpAnd t) d1 d2 ->
      emitBinaryOp t "and" d1 d2
    LowOpBinaryOp (BinaryOpOr t) d1 d2 ->
      emitBinaryOp t "or" d1 d2
    LowOpBinaryOp (BinaryOpXor t) d1 d2 ->
      emitBinaryOp t "xor" d1 d2
    LowOpBinaryOp (BinaryOpICmpEQ t) d1 d2 ->
      emitBinaryOp t "icmp eq" d1 d2
    LowOpBinaryOp (BinaryOpICmpNE t) d1 d2 ->
      emitBinaryOp t "icmp ne" d1 d2
    LowOpBinaryOp (BinaryOpICmpUGT t) d1 d2 ->
      emitBinaryOp t "icmp ugt" d1 d2
    LowOpBinaryOp (BinaryOpICmpUGE t) d1 d2 ->
      emitBinaryOp t "icmp uge" d1 d2
    LowOpBinaryOp (BinaryOpICmpULT t) d1 d2 ->
      emitBinaryOp t "icmp ult" d1 d2
    LowOpBinaryOp (BinaryOpICmpULE t) d1 d2 ->
      emitBinaryOp t "icmp ule" d1 d2
    LowOpBinaryOp (BinaryOpICmpSGT t) d1 d2 ->
      emitBinaryOp t "icmp sgt" d1 d2
    LowOpBinaryOp (BinaryOpICmpSGE t) d1 d2 ->
      emitBinaryOp t "icmp sge" d1 d2
    LowOpBinaryOp (BinaryOpICmpSLT t) d1 d2 ->
      emitBinaryOp t "icmp slt" d1 d2
    LowOpBinaryOp (BinaryOpICmpSLE t) d1 d2 ->
      emitBinaryOp t "icmp sle" d1 d2
    LowOpBinaryOp (BinaryOpFCmpFALSE t) d1 d2 ->
      emitBinaryOp t "fcmp false" d1 d2
    LowOpBinaryOp (BinaryOpFCmpOEQ t) d1 d2 ->
      emitBinaryOp t "fcmp oeq" d1 d2
    LowOpBinaryOp (BinaryOpFCmpOGT t) d1 d2 ->
      emitBinaryOp t "fcmp ogt" d1 d2
    LowOpBinaryOp (BinaryOpFCmpOGE t) d1 d2 ->
      emitBinaryOp t "fcmp oge" d1 d2
    LowOpBinaryOp (BinaryOpFCmpOLT t) d1 d2 ->
      emitBinaryOp t "fcmp olt" d1 d2
    LowOpBinaryOp (BinaryOpFCmpOLE t) d1 d2 ->
      emitBinaryOp t "fcmp ole" d1 d2
    LowOpBinaryOp (BinaryOpFCmpONE t) d1 d2 ->
      emitBinaryOp t "fcmp one" d1 d2
    LowOpBinaryOp (BinaryOpFCmpORD t) d1 d2 ->
      emitBinaryOp t "fcmp ord" d1 d2
    LowOpBinaryOp (BinaryOpFCmpUEQ t) d1 d2 ->
      emitBinaryOp t "fcmp ueq" d1 d2
    LowOpBinaryOp (BinaryOpFCmpUGT t) d1 d2 ->
      emitBinaryOp t "fcmp ugt" d1 d2
    LowOpBinaryOp (BinaryOpFCmpUGE t) d1 d2 ->
      emitBinaryOp t "fcmp uge" d1 d2
    LowOpBinaryOp (BinaryOpFCmpULT t) d1 d2 ->
      emitBinaryOp t "fcmp ult" d1 d2
    LowOpBinaryOp (BinaryOpFCmpULE t) d1 d2 ->
      emitBinaryOp t "fcmp ule" d1 d2
    LowOpBinaryOp (BinaryOpFCmpUNE t) d1 d2 ->
      emitBinaryOp t "fcmp une" d1 d2
    LowOpBinaryOp (BinaryOpFCmpUNO t) d1 d2 ->
      emitBinaryOp t "fcmp uno" d1 d2
    LowOpBinaryOp (BinaryOpFCmpTRUE t) d1 d2 ->
      emitBinaryOp t "fcmp true" d1 d2

emitUnaryOp :: LowType -> Builder -> LowValue -> WithEnv Builder
emitUnaryOp t inst d =
  return $ unwordsL [inst, showLowType t, showLowValue d]

emitBinaryOp :: LowType -> Builder -> LowValue -> LowValue -> WithEnv Builder
emitBinaryOp t inst d1 d2 =
  return $
    unwordsL [inst, showLowType t, showLowValue d1 <> ",", showLowValue d2]

emitLowCompConvOp :: Builder -> LowValue -> LowType -> LowType -> WithEnv Builder
emitLowCompConvOp cast d dom cod =
  return $
    unwordsL [cast, showLowType dom, showLowValue d, "to", showLowType cod]

emitSyscallOp :: Integer -> [LowValue] -> WithEnv Builder
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

emitOp :: Builder -> WithEnv [Builder]
emitOp s =
  return ["  " <> s]

emitRet :: Builder -> LowValue -> WithEnv [Builder]
emitRet retType d =
  emitOp $ unwordsL ["ret", retType, showLowValue d]

emitLabel :: Builder -> Builder
emitLabel s =
  s <> ":"

constructLabelList :: [a] -> WithEnv [Ident]
constructLabelList input =
  case input of
    [] ->
      return []
    (_ : rest) -> do
      label <- newNameWith' "case"
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
    <> showLowValue (LowValueLocal label)

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

getRegList :: WithEnv [Builder]
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
    LowValueLocal (I (_, i)) ->
      "%_" <> intDec i
    LowValueGlobal x ->
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
