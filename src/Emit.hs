{-# LANGUAGE OverloadedStrings #-}

module Emit
  ( emit
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.ByteString.Builder
import Data.Monoid ((<>))
import Numeric.Half

import qualified Data.ByteString.Lazy as L
import qualified Data.HashMap.Strict as Map
import qualified Data.Text.Encoding as TE

import Data.Basic
import Data.Env
import Data.LLVM

emit :: LLVM -> WithEnv L.ByteString
emit mainTerm = do
  lenv <- gets llvmEnv
  g <- emitGlobal
  let mainTerm' = reduceLLVM mainTerm
  zs <- emitDefinition "i64" "main" [] mainTerm'
  xs <-
    forM (Map.toList lenv) $ \(name, (args, body)) -> do
      let name' = asText' name
      let args' = map (showLLVMData . LLVMDataLocal) args
      let body' = reduceLLVM body
      emitDefinition "i8*" (TE.encodeUtf8Builder name') args' body'
  return $ toLazyByteString $ unlinesL $ g <> zs <> concat xs

emitDefinition :: Builder -> Builder -> [Builder] -> LLVM -> WithEnv [Builder]
emitDefinition retType name args asm = do
  let header = sig retType name args <> " {"
  content <- emitLLVM retType asm
  let footer = "}"
  return $ [header] <> content <> [footer]

sig :: Builder -> Builder -> [Builder] -> Builder
sig retType name args = "define " <> retType <> " @" <> name <> showLocals args

emitBlock :: Builder -> Identifier -> LLVM -> WithEnv [Builder]
emitBlock funName (I (_, i)) asm = do
  a <- emitLLVM funName asm
  return $ emitLabel ("_" <> intDec i) : a

emitLLVM :: Builder -> LLVM -> WithEnv [Builder]
emitLLVM retType (LLVMReturn d) = emitRet retType d
emitLLVM retType (LLVMCall f args) = do
  tmp <- newNameWith' "tmp"
  op <-
    emitOp $
    unwordsL
      [ showLLVMData (LLVMDataLocal tmp)
      , "="
      , "tail call i8*" -- fastcc?
      , showLLVMData f <> showArgs args
      ]
  a <- emitRet retType (LLVMDataLocal tmp)
  return $ op <> a
emitLLVM retType (LLVMSwitch (d, lowType) defaultBranch branchList) = do
  defaultLabel <- newNameWith' "default"
  labelList <- constructLabelList branchList
  op <-
    emitOp $
    unwordsL
      [ "switch"
      , showLowType lowType
      , showLLVMData d <> ","
      , "label"
      , showLLVMData (LLVMDataLocal defaultLabel)
      , showBranchList lowType $ zip (map fst branchList) labelList
      ]
  let asmList = map snd branchList
  xs <-
    forM (zip labelList asmList <> [(defaultLabel, defaultBranch)]) $
    uncurry (emitBlock retType)
  return $ op <> concat xs
emitLLVM retType (LLVMCont op cont) = do
  s <- emitLLVMOp op
  str <- emitOp s
  a <- emitLLVM retType cont
  return $ str <> a
emitLLVM retType (LLVMLet x op cont) = do
  s <- emitLLVMOp op
  str <- emitOp $ showLLVMData (LLVMDataLocal x) <> " = " <> s
  a <- emitLLVM retType cont
  return $ str <> a
emitLLVM _ LLVMUnreachable = emitOp $ unwordsL ["unreachable"]

emitLLVMOp :: LLVMOp -> WithEnv Builder
emitLLVMOp (LLVMOpCall d ds) = do
  return $ unwordsL ["call i8*", showLLVMData d <> showArgs ds]
emitLLVMOp (LLVMOpGetElementPtr (base, n) is) = do
  return $
    unwordsL
      [ "getelementptr"
      , showLowTypeAsIfNonPtr n <> ","
      -- , showLowType n <> "*"
      , showLowType n
      , showLLVMData base <> ","
      , showIndex is
      ]
emitLLVMOp (LLVMOpBitcast d fromType toType) =
  emitLLVMConvOp "bitcast" d fromType toType
emitLLVMOp (LLVMOpIntToPointer d fromType toType) =
  emitLLVMConvOp "inttoptr" d fromType toType
emitLLVMOp (LLVMOpPointerToInt d fromType toType) =
  emitLLVMConvOp "ptrtoint" d fromType toType
emitLLVMOp (LLVMOpLoad d lowType) = do
  return $
    unwordsL
      [ "load"
      , showLowType lowType <> ","
      , showLowTypeAsIfPtr lowType
      , showLLVMData d
      ]
emitLLVMOp (LLVMOpStore t d1 d2) = do
  return $
    unwordsL
      [ "store"
      , showLowType t
      , showLLVMData d1 <> ","
      , showLowTypeAsIfPtr t
      , showLLVMData d2
      ]
emitLLVMOp (LLVMOpAlloc d) = do
  return $ unwordsL ["call", "i8*", "@malloc(i64 " <> showLLVMData d <> ")"]
emitLLVMOp (LLVMOpFree d) = do
  return $ unwordsL ["call", "void", "@free(i8* " <> showLLVMData d <> ")"]
emitLLVMOp (LLVMOpSysCall num ds) = do
  emitSysCallOp num ds
emitLLVMOp (LLVMOpUnaryOp (UnaryOpNeg, t@(LowTypeFloat _)) d) = do
  emitUnaryOp t "fneg" d
emitLLVMOp (LLVMOpUnaryOp ((UnaryOpTrunc t2@(LowTypeIntS i2)), t1@(LowTypeIntS i1)) d)
  | i1 > i2 = emitLLVMConvOp "trunc" d t1 t2
emitLLVMOp (LLVMOpUnaryOp ((UnaryOpTrunc t2@(LowTypeIntU i2)), t1@(LowTypeIntU i1)) d)
  | i1 > i2 = emitLLVMConvOp "trunc" d t1 t2
emitLLVMOp (LLVMOpUnaryOp ((UnaryOpTrunc t2@(LowTypeFloat i2)), t1@(LowTypeFloat i1)) d)
  | sizeAsInt i1 > sizeAsInt i2 = emitLLVMConvOp "fptrunc" d t1 t2
emitLLVMOp (LLVMOpUnaryOp ((UnaryOpZext t2@(LowTypeIntS i2)), t1@(LowTypeIntS i1)) d)
  | i1 < i2 = emitLLVMConvOp "zext" d t1 t2
emitLLVMOp (LLVMOpUnaryOp ((UnaryOpZext t2@(LowTypeIntU i2)), t1@(LowTypeIntU i1)) d)
  | i1 < i2 = emitLLVMConvOp "zext" d t1 t2
emitLLVMOp (LLVMOpUnaryOp ((UnaryOpSext t2@(LowTypeIntS i2)), t1@(LowTypeIntS i1)) d)
  | i1 < i2 = emitLLVMConvOp "sext" d t1 t2
emitLLVMOp (LLVMOpUnaryOp ((UnaryOpSext t2@(LowTypeIntU i2)), t1@(LowTypeIntU i1)) d)
  | i1 < i2 = emitLLVMConvOp "sext" d t1 t2
emitLLVMOp (LLVMOpUnaryOp ((UnaryOpFpExt t2@(LowTypeFloat i2)), t1@(LowTypeFloat i1)) d)
  | sizeAsInt i1 < sizeAsInt i2 = emitLLVMConvOp "fpext" d t1 t2
emitLLVMOp (LLVMOpUnaryOp ((UnaryOpTo t2@(LowTypeFloat _)), t1@(LowTypeIntS _)) d) =
  emitLLVMConvOp "sitofp" d t1 t2
emitLLVMOp (LLVMOpUnaryOp ((UnaryOpTo t2@(LowTypeFloat _)), t1@(LowTypeIntU _)) d) =
  emitLLVMConvOp "uitofp" d t1 t2
emitLLVMOp (LLVMOpUnaryOp ((UnaryOpTo t2@(LowTypeIntS _)), t1@(LowTypeFloat _)) d) =
  emitLLVMConvOp "fptosi" d t1 t2
emitLLVMOp (LLVMOpUnaryOp ((UnaryOpTo t2@(LowTypeIntU _)), t1@(LowTypeFloat _)) d) =
  emitLLVMConvOp "fptoui" d t1 t2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpAdd, t@(LowTypeIntS _)) d1 d2) =
  emitBinaryOp t "add" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpAdd, t@(LowTypeIntU _)) d1 d2) =
  emitBinaryOp t "add" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpAdd, t@(LowTypeFloat _)) d1 d2) =
  emitBinaryOp t "fadd" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpSub, t@(LowTypeIntS _)) d1 d2) =
  emitBinaryOp t "sub" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpSub, t@(LowTypeIntU _)) d1 d2) =
  emitBinaryOp t "sub" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpSub, t@(LowTypeFloat _)) d1 d2) =
  emitBinaryOp t "fsub" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpMul, t@(LowTypeIntS _)) d1 d2) =
  emitBinaryOp t "mul" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpMul, t@(LowTypeIntU _)) d1 d2) =
  emitBinaryOp t "mul" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpMul, t@(LowTypeFloat _)) d1 d2) =
  emitBinaryOp t "fmul" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpDiv, t@(LowTypeIntS _)) d1 d2) =
  emitBinaryOp t "sdiv" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpDiv, t@(LowTypeIntU _)) d1 d2) =
  emitBinaryOp t "udiv" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpDiv, t@(LowTypeFloat _)) d1 d2) =
  emitBinaryOp t "fdiv" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpRem, t@(LowTypeIntS _)) d1 d2) =
  emitBinaryOp t "srem" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpRem, t@(LowTypeIntU _)) d1 d2) =
  emitBinaryOp t "urem" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpRem, t@(LowTypeFloat _)) d1 d2) =
  emitBinaryOp t "frem" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpEQ, t@(LowTypeIntS _)) d1 d2) =
  emitBinaryOp t "icmp eq" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpEQ, t@(LowTypeIntU _)) d1 d2) =
  emitBinaryOp t "icmp eq" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpEQ, t@(LowTypeFloat _)) d1 d2) =
  emitBinaryOp t "fcmp oeq" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpNE, t@(LowTypeIntS _)) d1 d2) =
  emitBinaryOp t "icmp ne" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpNE, t@(LowTypeIntU _)) d1 d2) =
  emitBinaryOp t "icmp ne" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpNE, t@(LowTypeFloat _)) d1 d2) =
  emitBinaryOp t "fcmp one" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpGT, t@(LowTypeIntS _)) d1 d2) =
  emitBinaryOp t "icmp sgt" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpGT, t@(LowTypeIntU _)) d1 d2) =
  emitBinaryOp t "icmp ugt" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpGT, t@(LowTypeFloat _)) d1 d2) =
  emitBinaryOp t "fcmp ogt" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpGE, t@(LowTypeIntS _)) d1 d2) =
  emitBinaryOp t "icmp sge" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpGE, t@(LowTypeIntU _)) d1 d2) =
  emitBinaryOp t "icmp uge" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpGE, t@(LowTypeFloat _)) d1 d2) =
  emitBinaryOp t "fcmp oge" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpLT, t@(LowTypeIntS _)) d1 d2) =
  emitBinaryOp t "icmp slt" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpLT, t@(LowTypeIntU _)) d1 d2) =
  emitBinaryOp t "icmp ult" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpLT, t@(LowTypeFloat _)) d1 d2) =
  emitBinaryOp t "fcmp olt" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpLE, t@(LowTypeIntS _)) d1 d2) =
  emitBinaryOp t "icmp sle" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpLE, t@(LowTypeIntU _)) d1 d2) =
  emitBinaryOp t "icmp ule" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpLE, t@(LowTypeFloat _)) d1 d2) =
  emitBinaryOp t "fcmp ole" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpShl, t@(LowTypeIntS _)) d1 d2) =
  emitBinaryOp t "shl" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpShl, t@(LowTypeIntU _)) d1 d2) =
  emitBinaryOp t "shl" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpLshr, t@(LowTypeIntS _)) d1 d2) =
  emitBinaryOp t "lshr" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpLshr, t@(LowTypeIntU _)) d1 d2) =
  emitBinaryOp t "lshr" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpAshr, t@(LowTypeIntS _)) d1 d2) =
  emitBinaryOp t "ashr" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpAshr, t@(LowTypeIntU _)) d1 d2) =
  emitBinaryOp t "ashr" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpAnd, t@(LowTypeIntS _)) d1 d2) =
  emitBinaryOp t "and" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpAnd, t@(LowTypeIntU _)) d1 d2) =
  emitBinaryOp t "and" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpOr, t@(LowTypeIntS _)) d1 d2) =
  emitBinaryOp t "or" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpOr, t@(LowTypeIntU _)) d1 d2) =
  emitBinaryOp t "or" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpXor, t@(LowTypeIntS _)) d1 d2) =
  emitBinaryOp t "xor" d1 d2
emitLLVMOp (LLVMOpBinaryOp (BinaryOpXor, t@(LowTypeIntU _)) d1 d2) =
  emitBinaryOp t "xor" d1 d2
emitLLVMOp _ = throwError' "emitLLVMOp"

emitUnaryOp :: LowType -> Builder -> LLVMData -> WithEnv Builder
emitUnaryOp t inst d = do
  return $ unwordsL [inst, showLowType t, showLLVMData d]

emitBinaryOp :: LowType -> Builder -> LLVMData -> LLVMData -> WithEnv Builder
emitBinaryOp t inst d1 d2 = do
  return $
    unwordsL [inst, showLowType t, showLLVMData d1 <> ",", showLLVMData d2]

emitLLVMConvOp :: Builder -> LLVMData -> LowType -> LowType -> WithEnv Builder
emitLLVMConvOp cast d dom cod = do
  return $
    unwordsL [cast, showLowType dom, showLLVMData d, "to", showLowType cod]

emitSysCallOp :: Integer -> [LLVMData] -> WithEnv Builder
emitSysCallOp num ds = do
  regList <- getRegList
  currentArch <- getArch
  case currentArch of
    Arch64 -> do
      let args = (LLVMDataInt num, LowTypeIntS 64) : zip ds (repeat voidPtr)
      let argStr = "(" <> showIndex args <> ")"
      let regStr = "\"=r" <> showRegList (take (length args) regList) <> "\""
      return $ unwordsL ["call i8* asm sideeffect \"syscall\",", regStr, argStr]

emitOp :: Builder -> WithEnv [Builder]
emitOp s = return ["  " <> s]

emitRet :: Builder -> LLVMData -> WithEnv [Builder]
emitRet retType d = emitOp $ unwordsL ["ret", retType, showLLVMData d]

emitLabel :: Builder -> Builder
emitLabel s = s <> ":"

constructLabelList :: [(Int, LLVM)] -> WithEnv [Identifier]
constructLabelList [] = return []
constructLabelList ((_, _):rest) = do
  label <- newNameWith' "case"
  labelList <- constructLabelList rest
  return $ label : labelList

showRegList :: [Builder] -> Builder
showRegList [] = ""
showRegList (s:ss) = ",{" <> s <> "}" <> showRegList ss

showBranchList :: LowType -> [(Int, Identifier)] -> Builder
showBranchList lowType xs =
  "[" <> showItems (uncurry (showBranch lowType)) xs <> "]"

showIndex :: [(LLVMData, LowType)] -> Builder
showIndex [] = ""
showIndex [(d, t)] = showLowType t <> " " <> showLLVMData d
showIndex ((d, t):dts) = showIndex [(d, t)] <> ", " <> showIndex dts

showBranch :: LowType -> Int -> Identifier -> Builder
showBranch lowType i label =
  showLowType lowType <>
  " " <> intDec i <> ", label " <> showLLVMData (LLVMDataLocal label)

showArg :: LLVMData -> Builder
showArg d = "i8* " <> showLLVMData d

showLocal :: Builder -> Builder
showLocal x = "i8* " <> x

showArgs :: [LLVMData] -> Builder
showArgs ds = "(" <> showItems showArg ds <> ")"

showLocals :: [Builder] -> Builder
showLocals ds = "(" <> showItems showLocal ds <> ")"

showLowTypeAsIfPtr :: LowType -> Builder
showLowTypeAsIfPtr t = showLowType t <> "*"

showLowTypeAsIfNonPtr :: LowType -> Builder
showLowTypeAsIfNonPtr (LowTypeIntS i) = "i" <> intDec i
showLowTypeAsIfNonPtr (LowTypeIntU i) = "i" <> intDec i
showLowTypeAsIfNonPtr (LowTypeFloat FloatSize16) = "half"
showLowTypeAsIfNonPtr (LowTypeFloat FloatSize32) = "float"
showLowTypeAsIfNonPtr (LowTypeFloat FloatSize64) = "double"
showLowTypeAsIfNonPtr LowTypeVoidPtr = "i8"
showLowTypeAsIfNonPtr (LowTypeStructPtr ts) =
  "{" <> showItems showLowType ts <> "}"
showLowTypeAsIfNonPtr (LowTypeFunctionPtr ts t) =
  showLowType t <> " (" <> showItems showLowType ts <> ")"
showLowTypeAsIfNonPtr (LowTypeArrayPtr i t) = do
  let s = showLowType t
  "[" <> intDec i <> " x " <> s <> "]"
showLowTypeAsIfNonPtr LowTypeIntS64Ptr = "i64"

-- for now
emitGlobal :: WithEnv [Builder]
emitGlobal = do
  os <- getOS
  case os of
    OSDarwin ->
      return
        [ "declare i8* @malloc(i64)"
        , "declare void @free(i8*)"
        -- The "direct" call of fork(2) via syscall seems to be broken in Darwin. It causes
        -- malloc after fork to be broken with message `mach_vm_map(size=1048576) failed (error code=268435459)`.
        -- Thus we need to declare the type of the interface function as follows and use it.
        , "declare i8* @fork()"
        ]
    _ -> return ["declare i8* @malloc(i64)", "declare void @free(i8*)"]

getRegList :: WithEnv [Builder]
getRegList = do
  targetOS <- getOS
  case targetOS of
    OSLinux -> return ["rax", "rdi", "rsi", "rdx", "rcx", "r8", "r9"]
    OSDarwin -> return ["rax", "rdi", "rsi", "rdx", "r10", "r8", "r9"]

showLowType :: LowType -> Builder
showLowType (LowTypeIntS i) = "i" <> intDec i
-- LLVM doesn't distinguish unsigned integers from signed ones
showLowType (LowTypeIntU i) = "i" <> intDec i
showLowType (LowTypeFloat FloatSize16) = "half"
showLowType (LowTypeFloat FloatSize32) = "float"
showLowType (LowTypeFloat FloatSize64) = "double"
showLowType LowTypeVoidPtr = "i8*"
showLowType (LowTypeStructPtr ts) = "{" <> showItems showLowType ts <> "}*"
showLowType (LowTypeFunctionPtr ts t) =
  showLowType t <> " (" <> showItems showLowType ts <> ")*"
showLowType (LowTypeArrayPtr i t) = do
  let s = showLowType t
  "[" <> intDec i <> " x " <> s <> "]*"
showLowType LowTypeIntS64Ptr = "i64*"

showLLVMData :: LLVMData -> Builder
showLLVMData (LLVMDataLocal (I (_, i))) = "%_" <> intDec i
showLLVMData (LLVMDataGlobal (I ("fork", 0))) = "@fork"
showLLVMData (LLVMDataGlobal x) = "@" <> TE.encodeUtf8Builder (asText' x)
showLLVMData (LLVMDataInt i) = integerDec i
showLLVMData (LLVMDataFloat16 x) = floatDec $ fromHalf x
showLLVMData (LLVMDataFloat32 x) = floatDec x
showLLVMData (LLVMDataFloat64 x) = doubleDec x
showLLVMData LLVMDataNull = "null"

showItems :: (a -> Builder) -> [a] -> Builder
showItems _ [] = ""
showItems f [a] = f a
showItems f (a:as) = f a <> ", " <> showItems f as

{-# INLINE unwordsL #-}
unwordsL :: [Builder] -> Builder
unwordsL [] = ""
unwordsL [b] = b
unwordsL (b:bs) = b <> " " <> unwordsL bs

{-# INLINE unlinesL #-}
unlinesL :: [Builder] -> Builder
unlinesL [] = ""
unlinesL [b] = b
unlinesL (b:bs) = b <> "\n" <> unlinesL bs
