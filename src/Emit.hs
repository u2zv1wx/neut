module Emit
  ( emit
  ) where

import Control.Monad.Except
import Control.Monad.State

import Data.Basic
import Data.Env
import Data.LLVM

emit :: LLVM -> WithEnv [String]
emit mainTerm = do
  lenv <- gets llvmEnv
  g <- emitGlobal
  zs <- emitDefinition "main" [] mainTerm
  xs <- forM lenv $ \(name, (args, body)) -> emitDefinition name args body
  return $ g ++ zs ++ concat xs

emitDefinition :: Identifier -> [Identifier] -> LLVM -> WithEnv [String]
emitDefinition name args asm = do
  let header = sig name args ++ " {"
  content <- emitLLVM name asm
  let footer = "}"
  return $ [header] ++ content ++ [footer]

sig :: Identifier -> [Identifier] -> String
sig "main" args = "define i64 @main" ++ showArgs (map LLVMDataLocal args)
sig name args =
  "define i8* " ++
  showLLVMData (LLVMDataGlobal name) ++ showArgs (map LLVMDataLocal args)

emitBlock :: Identifier -> Identifier -> LLVM -> WithEnv [String]
emitBlock funName name asm = do
  a <- emitLLVM funName asm
  return $ emitLabel name : a

-- FIXME: callはcall fastccにするべきっぽい？
emitLLVM :: Identifier -> LLVM -> WithEnv [String]
emitLLVM funName (LLVMReturn d) = emitRet funName d
emitLLVM funName (LLVMCall f args) = do
  tmp <- newNameWith "tmp"
  op <-
    emitOp $
    unwords
      [ showLLVMData (LLVMDataLocal tmp)
      , "="
      , "tail call i8*"
      , showLLVMData f ++ showArgs args
      ]
  a <- emitRet funName (LLVMDataLocal tmp)
  return $ op ++ a
emitLLVM funName (LLVMSwitch (d, lowType) defaultBranch branchList) = do
  defaultLabel <- newNameWith "default"
  labelList <- constructLabelList branchList
  op <-
    emitOp $
    unwords
      [ "switch"
      , showLowType lowType
      , showLLVMData d ++ ","
      , "label"
      , showLLVMData (LLVMDataLocal defaultLabel)
      , showBranchList lowType $ zip (map fst branchList) labelList
      ]
  let asmList = map snd branchList
  xs <-
    forM (zip labelList asmList ++ [(defaultLabel, defaultBranch)]) $
    uncurry (emitBlock funName)
  return $ op ++ concat xs
emitLLVM funName (LLVMCont op cont) = do
  s <- emitLLVMOp op
  str <- emitOp s
  a <- emitLLVM funName cont
  return $ str ++ a
emitLLVM funName (LLVMLet x op cont) = do
  s <- emitLLVMOp op
  str <- emitOp $ showLLVMData (LLVMDataLocal x) ++ " = " ++ s
  a <- emitLLVM funName cont
  return $ str ++ a
emitLLVM _ LLVMUnreachable = emitOp $ unwords ["unreachable"]

emitLLVMOp :: LLVMOp -> WithEnv String
emitLLVMOp (LLVMOpCall d ds) = do
  return $ unwords ["call i8*", showLLVMData d ++ showArgs ds]
emitLLVMOp (LLVMOpGetElementPtr (base, n) is) = do
  return $
    unwords
      [ "getelementptr"
      , showLowTypeAsIfNonPtr n ++ ","
      -- , showLowType n ++ "*"
      , showLowType n
      , showLLVMData base ++ ","
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
    unwords
      [ "load"
      , showLowType lowType ++ ","
      , showLowTypeAsIfPtr lowType
      , showLLVMData d
      ]
emitLLVMOp (LLVMOpStore t d1 d2) = do
  return $
    unwords
      [ "store"
      , showLowType t
      , showLLVMData d1 ++ ","
      , showLowTypeAsIfPtr t
      , showLLVMData d2
      ]
emitLLVMOp (LLVMOpAlloc d) = do
  return $ unwords ["call", "i8*", "@malloc(i64 " ++ showLLVMData d ++ ")"]
emitLLVMOp (LLVMOpFree d) = do
  return $ unwords ["call", "void", "@free(i8* " ++ showLLVMData d ++ ")"]
emitLLVMOp (LLVMOpSysCall ds) = do
  emitSysCallOp ds
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
emitLLVMOp _ = throwError "emitLLVMOp"

emitUnaryOp :: LowType -> String -> LLVMData -> WithEnv String
emitUnaryOp t inst d = do
  return $ unwords [inst, showLowType t, showLLVMData d]

emitBinaryOp :: LowType -> String -> LLVMData -> LLVMData -> WithEnv String
emitBinaryOp t inst d1 d2 = do
  return $
    unwords [inst, showLowType t, showLLVMData d1 ++ ",", showLLVMData d2]

emitLLVMConvOp :: String -> LLVMData -> LowType -> LowType -> WithEnv String
emitLLVMConvOp cast d dom cod = do
  return $
    unwords [cast, showLowType dom, showLLVMData d, "to", showLowType cod]

-- call i64 asm sideeffect "syscall", "=r,{rax},{rdi},{rsi},{rdx}" (i64 %raxArg, i64 %rdiArg, i64 %rsiArg, i64 %rdxArg)
emitSysCallOp :: [LLVMData] -> WithEnv String
emitSysCallOp ds = do
  regList <- getRegList
  currentArch <- getArch
  case currentArch of
    Arch64 ->
      return $
      unwords
        [ "call i8* asm sideeffect \"syscall\" \"=r,"
        , showRegList $ take (length ds) regList
        , "\" ("
        , showDataListWithType voidPtr ds
        , ")"
        ]

emitOp :: String -> WithEnv [String]
emitOp s = return ["  " ++ s]

emitRet :: Identifier -> LLVMData -> WithEnv [String]
emitRet "main" d = emitOp $ unwords ["ret i64", showLLVMData d]
emitRet _ d = emitOp $ unwords ["ret i8*", showLLVMData d]

emitLabel :: String -> String
emitLabel s = s ++ ":"

constructLabelList :: [(Int, LLVM)] -> WithEnv [String]
constructLabelList [] = return []
constructLabelList ((_, _):rest) = do
  label <- newNameWith "case"
  labelList <- constructLabelList rest
  return $ label : labelList

showRegList :: [String] -> String
showRegList [] = ""
showRegList [s] = "{" ++ s ++ "}"
showRegList (s:ss) = "{" ++ s ++ "}," ++ showRegList ss

showBranchList :: LowType -> [(Int, String)] -> String
showBranchList lowType xs =
  "[" ++ showItems (uncurry (showBranch lowType)) xs ++ "]"

showDataListWithType :: LowType -> [LLVMData] -> String
showDataListWithType t ds = showIndex $ zip ds (repeat t)

showIndex :: [(LLVMData, LowType)] -> String
showIndex [] = ""
showIndex [(d, t)] = showLowType t ++ " " ++ showLLVMData d
showIndex ((d, t):dts) = showIndex [(d, t)] ++ ", " ++ showIndex dts

-- showIndex ds = showDataListWithType (LowTypeIntS 64) ds
showBranch :: LowType -> Int -> String -> String
showBranch lowType i label =
  showLowType lowType ++
  " " ++ show i ++ ", label " ++ showLLVMData (LLVMDataLocal label)

showArg :: LLVMData -> String
showArg d = "i8* " ++ showLLVMData d

showArgs :: [LLVMData] -> String
showArgs ds = "(" ++ showItems showArg ds ++ ")"

showLowTypeAsIfPtr :: LowType -> String
showLowTypeAsIfPtr t = showLowType t ++ "*"

showLowTypeAsIfNonPtr :: LowType -> String
showLowTypeAsIfNonPtr t = init $ showLowType t

-- for now
emitGlobal :: WithEnv [String]
emitGlobal = return ["declare i8* @malloc(i64)", "declare void @free(i8*)"]

getRegList :: WithEnv [String]
getRegList = do
  targetOS <- getOS
  case targetOS of
    OSLinux -> return ["rax", "rdi", "rsi", "rdx", "rcx", "r8", "r9"]
    OSDarwin -> return ["rax", "rdi", "rsi", "rdx", "r10", "r8", "r9"]
