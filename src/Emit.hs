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
import Data.LLVM
import qualified Data.Map as Map
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Numeric.Half
import Reduce.LLVM

emit :: LLVM -> WithEnv Builder
emit mainTerm = do
  lenv <- gets llvmEnv
  g <- emitDeclarations
  mainTerm' <- reduceLLVM IntMap.empty Map.empty mainTerm
  zs <- emitDefinition "i64" "main" [] mainTerm'
  xs <-
    forM (HashMap.toList lenv) $ \(name, (args, body)) -> do
      -- ここも非同期でやれる
      let args' = map (showLLVMData . LLVMDataLocal) args
      body' <- reduceLLVM IntMap.empty Map.empty body
      emitDefinition "i8*" (TE.encodeUtf8Builder name) args' body'
  return $ unlinesL $ g : zs <> concat xs

emitDeclarations :: WithEnv Builder
emitDeclarations = do
  denv <- HashMap.toList <$> gets declEnv
  return $ unlinesL $ map declToBuilder denv

declToBuilder :: (T.Text, ([LowType], LowType)) -> Builder
declToBuilder (name, (dom, cod)) = do
  let name' = TE.encodeUtf8Builder name
  "declare "
    <> showLowType cod
    <> " @"
    <> name'
    <> "("
    <> showItems showLowType dom
    <> ")"

emitDefinition :: Builder -> Builder -> [Builder] -> LLVM -> WithEnv [Builder]
emitDefinition retType name args asm = do
  let header = sig retType name args <> " {"
  content <- emitLLVM retType asm
  let footer = "}"
  return $ [header] <> content <> [footer]

sig :: Builder -> Builder -> [Builder] -> Builder
sig retType name args =
  "define " <> retType <> " @" <> name <> showLocals args

emitBlock :: Builder -> Ident -> LLVM -> WithEnv [Builder]
emitBlock funName (I (_, i)) asm = do
  a <- emitLLVM funName asm
  return $ emitLabel ("_" <> intDec i) : a

emitLLVM :: Builder -> LLVM -> WithEnv [Builder]
emitLLVM retType llvm =
  case llvm of
    LLVMReturn d ->
      emitRet retType d
    LLVMCall f args -> do
      tmp <- newNameWith' "tmp"
      op <-
        emitOp $
          unwordsL
            [ showLLVMData (LLVMDataLocal tmp),
              "=",
              "tail call fastcc i8*",
              showLLVMData f <> showArgs args
            ]
      a <- emitRet retType (LLVMDataLocal tmp)
      return $ op <> a
    LLVMSwitch (d, lowType) defaultBranch branchList -> do
      defaultLabel <- newNameWith' "default"
      labelList <- constructLabelList branchList
      op <-
        emitOp $
          unwordsL
            [ "switch",
              showLowType lowType,
              showLLVMData d <> ",",
              "label",
              showLLVMData (LLVMDataLocal defaultLabel),
              showBranchList lowType $ zip (map fst branchList) labelList
            ]
      let asmList = map snd branchList
      xs <-
        forM (zip labelList asmList <> [(defaultLabel, defaultBranch)]) $
          uncurry (emitBlock retType)
      return $ op <> concat xs
    LLVMBranch d onTrue onFalse -> do
      onTrueLabel <- newNameWith' "case-true"
      onFalseLabel <- newNameWith' "case-false"
      op <-
        emitOp $
          unwordsL
            [ "br",
              "i1",
              showLLVMData d <> ",",
              "label",
              showLLVMData (LLVMDataLocal onTrueLabel) <> ",",
              "label",
              showLLVMData (LLVMDataLocal onFalseLabel)
            ]
      xs <-
        forM [(onTrueLabel, onTrue), (onFalseLabel, onFalse)] $
          uncurry (emitBlock retType)
      return $ op <> concat xs
    LLVMCont (LLVMOpFree d _ j) cont -> do
      nenv <- gets nopFreeSet
      if S.member j nenv
        then emitLLVM retType cont
        else do
          str <-
            emitOp $
              unwordsL ["call fastcc", "void", "@free(i8* " <> showLLVMData d <> ")"]
          a <- emitLLVM retType cont
          return $ str <> a
    LLVMCont op cont -> do
      s <- emitLLVMOp op
      str <- emitOp s
      a <- emitLLVM retType cont
      return $ str <> a
    LLVMLet x op cont -> do
      s <- emitLLVMOp op
      str <- emitOp $ showLLVMData (LLVMDataLocal x) <> " = " <> s
      a <- emitLLVM retType cont
      return $ str <> a
    LLVMUnreachable ->
      emitOp $ unwordsL ["unreachable"]

emitLLVMOp :: LLVMOp -> WithEnv Builder
emitLLVMOp llvmOp =
  case llvmOp of
    LLVMOpCall d ds ->
      return $ unwordsL ["call fastcc i8*", showLLVMData d <> showArgs ds]
    LLVMOpGetElementPtr (base, n) is ->
      return $
        unwordsL
          [ "getelementptr",
            showLowTypeAsIfNonPtr n <> ",",
            showLowType n,
            showLLVMData base <> ",",
            showIndex is
          ]
    LLVMOpBitcast d fromType toType ->
      emitLLVMConvOp "bitcast" d fromType toType
    LLVMOpIntToPointer d fromType toType ->
      emitLLVMConvOp "inttoptr" d fromType toType
    LLVMOpPointerToInt d fromType toType ->
      emitLLVMConvOp "ptrtoint" d fromType toType
    LLVMOpLoad d lowType ->
      return $
        unwordsL
          [ "load",
            showLowType lowType <> ",",
            showLowTypeAsIfPtr lowType,
            showLLVMData d
          ]
    LLVMOpStore t d1 d2 ->
      return $
        unwordsL
          [ "store",
            showLowType t,
            showLLVMData d1 <> ",",
            showLowTypeAsIfPtr t,
            showLLVMData d2
          ]
    LLVMOpAlloc d _ ->
      return $ unwordsL ["call fastcc", "i8*", "@malloc(i64 " <> showLLVMData d <> ")"]
    LLVMOpSysCall num ds ->
      emitSysCallOp num ds
    LLVMOpUnaryOp (UnaryOpNeg t@(LowTypeFloat _)) d ->
      emitUnaryOp t "fneg" d
    LLVMOpUnaryOp (UnaryOpTrunc t1@(LowTypeIntS i1) t2@(LowTypeIntS i2)) d
      | i1 > i2 -> emitLLVMConvOp "trunc" d t1 t2
    LLVMOpUnaryOp (UnaryOpTrunc t1@(LowTypeIntU i1) t2@(LowTypeIntU i2)) d
      | i1 > i2 -> emitLLVMConvOp "trunc" d t1 t2
    LLVMOpUnaryOp (UnaryOpTrunc t1@(LowTypeFloat i1) t2@(LowTypeFloat i2)) d
      | sizeAsInt i1 > sizeAsInt i2 -> emitLLVMConvOp "fptrunc" d t1 t2
    LLVMOpUnaryOp (UnaryOpZext t1@(LowTypeIntS i1) t2@(LowTypeIntS i2)) d
      | i1 < i2 -> emitLLVMConvOp "zext" d t1 t2
    LLVMOpUnaryOp (UnaryOpZext t1@(LowTypeIntU i1) t2@(LowTypeIntU i2)) d
      | i1 < i2 -> emitLLVMConvOp "zext" d t1 t2
    LLVMOpUnaryOp (UnaryOpSext t1@(LowTypeIntS i1) t2@(LowTypeIntS i2)) d
      | i1 < i2 -> emitLLVMConvOp "sext" d t1 t2
    LLVMOpUnaryOp (UnaryOpSext t1@(LowTypeIntU i1) t2@(LowTypeIntU i2)) d
      | i1 < i2 -> emitLLVMConvOp "sext" d t1 t2
    LLVMOpUnaryOp (UnaryOpFpExt t1@(LowTypeFloat i1) t2@(LowTypeFloat i2)) d
      | sizeAsInt i1 < sizeAsInt i2 -> emitLLVMConvOp "fpext" d t1 t2
    LLVMOpUnaryOp (UnaryOpTo t1@(LowTypeIntS _) t2@(LowTypeFloat _)) d ->
      emitLLVMConvOp "sitofp" d t1 t2
    LLVMOpUnaryOp (UnaryOpTo t1@(LowTypeIntU _) t2@(LowTypeFloat _)) d ->
      emitLLVMConvOp "uitofp" d t1 t2
    LLVMOpUnaryOp (UnaryOpTo t1@(LowTypeFloat _) t2@(LowTypeIntS _)) d ->
      emitLLVMConvOp "fptosi" d t1 t2
    LLVMOpUnaryOp (UnaryOpTo t1@(LowTypeFloat _) t2@(LowTypeIntU _)) d ->
      emitLLVMConvOp "fptoui" d t1 t2
    LLVMOpBinaryOp (BinaryOpAdd t@(LowTypeIntS _)) d1 d2 ->
      emitBinaryOp t "add" d1 d2
    LLVMOpBinaryOp (BinaryOpAdd t@(LowTypeIntU _)) d1 d2 ->
      emitBinaryOp t "add" d1 d2
    LLVMOpBinaryOp (BinaryOpAdd t@(LowTypeFloat _)) d1 d2 ->
      emitBinaryOp t "fadd" d1 d2
    LLVMOpBinaryOp (BinaryOpSub t@(LowTypeIntS _)) d1 d2 ->
      emitBinaryOp t "sub" d1 d2
    LLVMOpBinaryOp (BinaryOpSub t@(LowTypeIntU _)) d1 d2 ->
      emitBinaryOp t "sub" d1 d2
    LLVMOpBinaryOp (BinaryOpSub t@(LowTypeFloat _)) d1 d2 ->
      emitBinaryOp t "fsub" d1 d2
    LLVMOpBinaryOp (BinaryOpMul t@(LowTypeIntS _)) d1 d2 ->
      emitBinaryOp t "mul" d1 d2
    LLVMOpBinaryOp (BinaryOpMul t@(LowTypeIntU _)) d1 d2 ->
      emitBinaryOp t "mul" d1 d2
    LLVMOpBinaryOp (BinaryOpMul t@(LowTypeFloat _)) d1 d2 ->
      emitBinaryOp t "fmul" d1 d2
    LLVMOpBinaryOp (BinaryOpDiv t@(LowTypeIntS _)) d1 d2 ->
      emitBinaryOp t "sdiv" d1 d2
    LLVMOpBinaryOp (BinaryOpDiv t@(LowTypeIntU _)) d1 d2 ->
      emitBinaryOp t "udiv" d1 d2
    LLVMOpBinaryOp (BinaryOpDiv t@(LowTypeFloat _)) d1 d2 ->
      emitBinaryOp t "fdiv" d1 d2
    LLVMOpBinaryOp (BinaryOpRem t@(LowTypeIntS _)) d1 d2 ->
      emitBinaryOp t "srem" d1 d2
    LLVMOpBinaryOp (BinaryOpRem t@(LowTypeIntU _)) d1 d2 ->
      emitBinaryOp t "urem" d1 d2
    LLVMOpBinaryOp (BinaryOpRem t@(LowTypeFloat _)) d1 d2 ->
      emitBinaryOp t "frem" d1 d2
    LLVMOpBinaryOp (BinaryOpEQ t@(LowTypeIntS _)) d1 d2 ->
      emitBinaryOp t "icmp eq" d1 d2
    LLVMOpBinaryOp (BinaryOpEQ t@(LowTypeIntU _)) d1 d2 ->
      emitBinaryOp t "icmp eq" d1 d2
    LLVMOpBinaryOp (BinaryOpEQ t@(LowTypePtr (LowTypeIntS 8))) d1 d2 ->
      emitBinaryOp t "icmp eq" d1 d2
    LLVMOpBinaryOp (BinaryOpEQ t@(LowTypeFloat _)) d1 d2 ->
      emitBinaryOp t "fcmp oeq" d1 d2
    LLVMOpBinaryOp (BinaryOpNE t@(LowTypeIntS _)) d1 d2 ->
      emitBinaryOp t "icmp ne" d1 d2
    LLVMOpBinaryOp (BinaryOpNE t@(LowTypeIntU _)) d1 d2 ->
      emitBinaryOp t "icmp ne" d1 d2
    LLVMOpBinaryOp (BinaryOpNE t@(LowTypePtr (LowTypeIntS 8))) d1 d2 ->
      emitBinaryOp t "icmp ne" d1 d2
    LLVMOpBinaryOp (BinaryOpNE t@(LowTypeFloat _)) d1 d2 ->
      emitBinaryOp t "fcmp one" d1 d2
    LLVMOpBinaryOp (BinaryOpGT t@(LowTypeIntS _)) d1 d2 ->
      emitBinaryOp t "icmp sgt" d1 d2
    LLVMOpBinaryOp (BinaryOpGT t@(LowTypeIntU _)) d1 d2 ->
      emitBinaryOp t "icmp ugt" d1 d2
    LLVMOpBinaryOp (BinaryOpGT t@(LowTypeFloat _)) d1 d2 ->
      emitBinaryOp t "fcmp ogt" d1 d2
    LLVMOpBinaryOp (BinaryOpGE t@(LowTypeIntS _)) d1 d2 ->
      emitBinaryOp t "icmp sge" d1 d2
    LLVMOpBinaryOp (BinaryOpGE t@(LowTypeIntU _)) d1 d2 ->
      emitBinaryOp t "icmp uge" d1 d2
    LLVMOpBinaryOp (BinaryOpGE t@(LowTypeFloat _)) d1 d2 ->
      emitBinaryOp t "fcmp oge" d1 d2
    LLVMOpBinaryOp (BinaryOpLT t@(LowTypeIntS _)) d1 d2 ->
      emitBinaryOp t "icmp slt" d1 d2
    LLVMOpBinaryOp (BinaryOpLT t@(LowTypeIntU _)) d1 d2 ->
      emitBinaryOp t "icmp ult" d1 d2
    LLVMOpBinaryOp (BinaryOpLT t@(LowTypeFloat _)) d1 d2 ->
      emitBinaryOp t "fcmp olt" d1 d2
    LLVMOpBinaryOp (BinaryOpLE t@(LowTypeIntS _)) d1 d2 ->
      emitBinaryOp t "icmp sle" d1 d2
    LLVMOpBinaryOp (BinaryOpLE t@(LowTypeIntU _)) d1 d2 ->
      emitBinaryOp t "icmp ule" d1 d2
    LLVMOpBinaryOp (BinaryOpLE t@(LowTypeFloat _)) d1 d2 ->
      emitBinaryOp t "fcmp ole" d1 d2
    LLVMOpBinaryOp (BinaryOpShl t@(LowTypeIntS _)) d1 d2 ->
      emitBinaryOp t "shl" d1 d2
    LLVMOpBinaryOp (BinaryOpShl t@(LowTypeIntU _)) d1 d2 ->
      emitBinaryOp t "shl" d1 d2
    LLVMOpBinaryOp (BinaryOpLshr t@(LowTypeIntS _)) d1 d2 ->
      emitBinaryOp t "lshr" d1 d2
    LLVMOpBinaryOp (BinaryOpLshr t@(LowTypeIntU _)) d1 d2 ->
      emitBinaryOp t "lshr" d1 d2
    LLVMOpBinaryOp (BinaryOpAshr t@(LowTypeIntS _)) d1 d2 ->
      emitBinaryOp t "ashr" d1 d2
    LLVMOpBinaryOp (BinaryOpAshr t@(LowTypeIntU _)) d1 d2 ->
      emitBinaryOp t "ashr" d1 d2
    LLVMOpBinaryOp (BinaryOpAnd t@(LowTypeIntS _)) d1 d2 ->
      emitBinaryOp t "and" d1 d2
    LLVMOpBinaryOp (BinaryOpAnd t@(LowTypeIntU _)) d1 d2 ->
      emitBinaryOp t "and" d1 d2
    LLVMOpBinaryOp (BinaryOpOr t@(LowTypeIntS _)) d1 d2 ->
      emitBinaryOp t "or" d1 d2
    LLVMOpBinaryOp (BinaryOpOr t@(LowTypeIntU _)) d1 d2 ->
      emitBinaryOp t "or" d1 d2
    LLVMOpBinaryOp (BinaryOpXor t@(LowTypeIntS _)) d1 d2 ->
      emitBinaryOp t "xor" d1 d2
    LLVMOpBinaryOp (BinaryOpXor t@(LowTypeIntU _)) d1 d2 ->
      emitBinaryOp t "xor" d1 d2
    foo -> do
      p' foo
      raiseCritical' "ill-typed LLVMOp"

emitUnaryOp :: LowType -> Builder -> LLVMData -> WithEnv Builder
emitUnaryOp t inst d =
  return $ unwordsL [inst, showLowType t, showLLVMData d]

emitBinaryOp :: LowType -> Builder -> LLVMData -> LLVMData -> WithEnv Builder
emitBinaryOp t inst d1 d2 =
  return $
    unwordsL [inst, showLowType t, showLLVMData d1 <> ",", showLLVMData d2]

emitLLVMConvOp :: Builder -> LLVMData -> LowType -> LowType -> WithEnv Builder
emitLLVMConvOp cast d dom cod =
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
      return $
        unwordsL ["call fastcc i8* asm sideeffect \"syscall\",", regStr, argStr]

emitOp :: Builder -> WithEnv [Builder]
emitOp s =
  return ["  " <> s]

emitRet :: Builder -> LLVMData -> WithEnv [Builder]
emitRet retType d =
  emitOp $ unwordsL ["ret", retType, showLLVMData d]

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
  "[" <> showItems (uncurry (showBranch lowType)) xs <> "]"

showIndex :: [(LLVMData, LowType)] -> Builder
showIndex idxList =
  case idxList of
    [] ->
      ""
    [(d, t)] ->
      showLowType t <> " " <> showLLVMData d
    ((d, t) : dts) ->
      showIndex [(d, t)] <> ", " <> showIndex dts

showBranch :: LowType -> Int -> Ident -> Builder
showBranch lowType i label =
  showLowType lowType
    <> " "
    <> intDec i
    <> ", label "
    <> showLLVMData (LLVMDataLocal label)

showArg :: LLVMData -> Builder
showArg d =
  "i8* " <> showLLVMData d

showLocal :: Builder -> Builder
showLocal x =
  "i8* " <> x

showArgs :: [LLVMData] -> Builder
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
    LowTypeIntS i ->
      "i" <> intDec i
    LowTypeIntU i ->
      "i" <> intDec i
    LowTypeFloat FloatSize16 ->
      "half"
    LowTypeFloat FloatSize32 ->
      "float"
    LowTypeFloat FloatSize64 ->
      "double"
    LowTypeVoid ->
      "void"
    LowTypeStruct ts ->
      "{" <> showItems showLowType ts <> "}"
    LowTypeFunctionPtr ts t ->
      showLowType t <> " (" <> showItems showLowType ts <> ")"
    LowTypeArray i t -> do
      let s = showLowType t
      "[" <> intDec i <> " x " <> s <> "]"
    LowTypePtr t ->
      showLowType t

getRegList :: WithEnv [Builder]
getRegList = do
  targetOS <- getOS
  case targetOS of
    OSLinux ->
      return ["rax", "rdi", "rsi", "rdx", "rcx", "r8", "r9"]
    OSDarwin ->
      return ["rax", "rdi", "rsi", "rdx", "r10", "r8", "r9"]

showLowType :: LowType -> Builder
showLowType lowType =
  case lowType of
    LowTypeIntS i ->
      "i" <> intDec i
    -- LLVM doesn't distinguish unsigned integers from signed ones
    LowTypeIntU i ->
      "i" <> intDec i
    LowTypeFloat FloatSize16 ->
      "half"
    LowTypeFloat FloatSize32 ->
      "float"
    LowTypeFloat FloatSize64 ->
      "double"
    LowTypeVoid ->
      "void"
    LowTypeStruct ts ->
      "{" <> showItems showLowType ts <> "}"
    LowTypeFunctionPtr ts t ->
      showLowType t <> " (" <> showItems showLowType ts <> ")*"
    LowTypeArray i t -> do
      let s = showLowType t
      "[" <> intDec i <> " x " <> s <> "]"
    LowTypePtr t ->
      showLowType t <> "*"

showLLVMData :: LLVMData -> Builder
showLLVMData llvmData =
  case llvmData of
    LLVMDataLocal (I (_, i)) ->
      "%_" <> intDec i
    LLVMDataGlobal x ->
      "@" <> TE.encodeUtf8Builder x
    LLVMDataInt i ->
      integerDec i
    LLVMDataFloat FloatSize16 x -> do
      let x' = realToFrac x :: Half
      "0x" <> doubleHexFixed (realToFrac x')
    LLVMDataFloat FloatSize32 x -> do
      let x' = realToFrac x :: Float
      "0x" <> doubleHexFixed (realToFrac x')
    LLVMDataFloat FloatSize64 x -> do
      let x' = realToFrac x :: Double
      "0x" <> doubleHexFixed (realToFrac x')
    LLVMDataNull ->
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
