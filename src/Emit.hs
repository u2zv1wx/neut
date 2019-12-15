module Emit
  ( emit
  ) where

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
  let prologue = sig name args ++ " {"
  content <- emitLLVM name asm
  let epilogue = "}"
  return $ [prologue] ++ content ++ [epilogue]

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
emitLLVM funName (LLVMSwitch d defaultBranch branchList) = do
  defaultLabel <- newNameWith "default"
  labelList <- constructLabelList branchList
  op <-
    emitOp $
    unwords
      [ "switch"
      , "i64"
      , showLLVMData d ++ ","
      , "label"
      , showLLVMData (LLVMDataLocal defaultLabel)
      , showBranchList $ zip (map fst branchList) labelList
      ]
  let asmList = map snd branchList
  xs <-
    forM (zip labelList asmList ++ [(defaultLabel, defaultBranch)]) $
    uncurry (emitBlock funName)
  return $ op ++ concat xs
emitLLVM funName (LLVMReturn d) = emitRet funName d
emitLLVM funName (LLVMLet x (LLVMCall f args) cont) = do
  op <-
    emitOp $
    unwords
      [ showLLVMData (LLVMDataLocal x)
      , "="
      , "call i8*"
      , showLLVMData f ++ showArgs args
      ]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMSwitch d defaultBranch branchList) cont) = do
  let (labelList, ls) = unzip branchList
  let ls' = map (\l -> LLVMLet x l cont) ls
  let defaultBranch' = LLVMLet x defaultBranch cont
  emitLLVM funName (LLVMSwitch d defaultBranch' (zip labelList ls'))
emitLLVM funName (LLVMLet x (LLVMReturn d) cont)
  -- by the definition of LLVM.hs, the type of `d` is always `i8*`.
 = emitLLVM funName (LLVMLet x (LLVMBitcast d voidPtr voidPtr) cont)
emitLLVM funName (LLVMLet x (LLVMLet y cont1 cont2) cont3) =
  emitLLVM funName (LLVMLet y cont1 (LLVMLet x cont2 cont3))
emitLLVM funName (LLVMLet x (LLVMGetElementPtr base (i, n)) cont) = do
  op <-
    emitOp $
    unwords
      [ showLLVMData (LLVMDataLocal x)
      , "= getelementptr"
      , showStruct n ++ ","
      , showStruct n ++ "*"
      , showLLVMData base ++ ","
      , showIndex [0, i]
      ]
  xs <- emitLLVM funName cont
  return $ op ++ xs
emitLLVM funName (LLVMLet x (LLVMBitcast d fromType toType) cont) = do
  op <-
    emitOp $
    unwords
      [ showLLVMData (LLVMDataLocal x)
      , "="
      , "bitcast"
      , showLowTypeEmit fromType
      , showLLVMData d
      , "to"
      , showLowTypeEmit toType
      ]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMIntToPointer d fromType toType) cont) = do
  op <-
    emitOp $
    unwords
      [ showLLVMData (LLVMDataLocal x)
      , "="
      , "inttoptr"
      , showLowTypeEmit fromType
      , showLLVMData d
      , "to"
      , showLowTypeEmit toType
      ]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMPointerToInt d fromType toType) cont) = do
  op <-
    emitOp $
    unwords
      [ showLLVMData (LLVMDataLocal x)
      , "="
      , "ptrtoint"
      , showLowTypeEmit fromType
      , showLLVMData d
      , "to"
      , showLowTypeEmit toType
      ]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMLoad d) cont) = do
  op <-
    emitOp $
    unwords
      [showLLVMData (LLVMDataLocal x), "=", "load i8*, i8**", showLLVMData d]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet _ (LLVMStore (d1, t1) (d2, t2)) cont) = do
  op <-
    emitOp $
    unwords
      [ "store"
      , showLowTypeEmit t1
      , showLLVMData d1 ++ ","
      , showLowTypeEmit t2
      , showLLVMData d2
      ]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMAlloc len) cont) = do
  size <- newNameWith "sizeptr"
  -- Use getelementptr to realize `sizeof`. More info:
  --   http://nondot.org/sabre/LLVMNotes/SizeOf-OffsetOf-VariableSizedStructs.txt
  op1 <-
    emitOp $
    unwords
      [ showLLVMData (LLVMDataLocal size)
      , "="
      , "getelementptr i64, i64* null, i32 " ++ show len
      ]
  casted <- newNameWith "size"
  op2 <-
    emitOp $
    unwords
      [ showLLVMData (LLVMDataLocal casted)
      , "="
      , "ptrtoint i64*"
      , showLLVMData (LLVMDataLocal size)
      , "to i64"
      ]
  op3 <-
    emitOp $
    unwords
      [ showLLVMData (LLVMDataLocal x)
      , "="
      , "call"
      , "i8*"
      , "@malloc(i64 " ++ showLLVMData (LLVMDataLocal casted) ++ ")"
      ]
  a <- emitLLVM funName cont
  return $ op1 ++ op2 ++ op3 ++ a
emitLLVM funName (LLVMLet _ (LLVMFree d) cont) = do
  op <- emitOp $ unwords ["call", "void", "@free(i8* " ++ showLLVMData d ++ ")"]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMArith (ArithAdd, t@(LowTypeSignedInt _)) d1 d2) cont) = do
  op <-
    emitOp $
    unwords
      [ showLLVMData (LLVMDataLocal x)
      , "="
      , "add"
      , showLowTypeEmit t
      , showLLVMData d1 ++ ","
      , showLLVMData d2
      ]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMArith (ArithAdd, LowTypeUnsignedInt size) d1 d2) cont) =
  emitLLVM
    funName
    (LLVMLet x (LLVMArith (ArithAdd, LowTypeSignedInt size) d1 d2) cont) -- thanks to the two's complement representation
emitLLVM funName (LLVMLet x (LLVMArith (ArithAdd, t) d1 d2) cont) = do
  op <-
    emitOp $
    unwords
      [ showLLVMData (LLVMDataLocal x)
      , "="
      , "fadd"
      , showLowTypeEmit t
      , showLLVMData d1 ++ ","
      , showLLVMData d2
      ]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMArith (ArithSub, t@(LowTypeSignedInt _)) d1 d2) cont) = do
  op <-
    emitOp $
    unwords
      [ showLLVMData (LLVMDataLocal x)
      , "="
      , "sub"
      , showLowTypeEmit t
      , showLLVMData d1 ++ ","
      , showLLVMData d2
      ]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMArith (ArithSub, LowTypeUnsignedInt size) d1 d2) cont) =
  emitLLVM
    funName
    (LLVMLet x (LLVMArith (ArithSub, LowTypeSignedInt size) d1 d2) cont) -- thanks to the two's complement representation
emitLLVM funName (LLVMLet x (LLVMArith (ArithSub, t) d1 d2) cont) = do
  op <-
    emitOp $
    unwords
      [ showLLVMData (LLVMDataLocal x)
      , "="
      , "fsub"
      , showLowTypeEmit t
      , showLLVMData d1 ++ ","
      , showLLVMData d2
      ]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMArith (ArithMul, t@(LowTypeSignedInt _)) d1 d2) cont) = do
  op <-
    emitOp $
    unwords
      [ showLLVMData (LLVMDataLocal x)
      , "="
      , "mul"
      , showLowTypeEmit t
      , showLLVMData d1 ++ ","
      , showLLVMData d2
      ]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMArith (ArithMul, LowTypeUnsignedInt size) d1 d2) cont) =
  emitLLVM
    funName
    (LLVMLet x (LLVMArith (ArithMul, LowTypeSignedInt size) d1 d2) cont) -- thanks to the two's complement representation
emitLLVM funName (LLVMLet x (LLVMArith (ArithMul, t) d1 d2) cont) = do
  op <-
    emitOp $
    unwords
      [ showLLVMData (LLVMDataLocal x)
      , "="
      , "fmul"
      , showLowTypeEmit t
      , showLLVMData d1 ++ ","
      , showLLVMData d2
      ]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMArith (ArithDiv, t@(LowTypeSignedInt _)) d1 d2) cont) = do
  op <-
    emitOp $
    unwords
      [ showLLVMData (LLVMDataLocal x)
      , "="
      , "sdiv"
      , showLowTypeEmit t
      , showLLVMData d1 ++ ","
      , showLLVMData d2
      ]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMArith (ArithDiv, t@(LowTypeUnsignedInt _)) d1 d2) cont) = do
  op <-
    emitOp $
    unwords
      [ showLLVMData (LLVMDataLocal x)
      , "="
      , "udiv"
      , showLowTypeEmit t
      , showLLVMData d1 ++ ","
      , showLLVMData d2
      ]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMArith (ArithDiv, t) d1 d2) cont) = do
  op <-
    emitOp $
    unwords
      [ showLLVMData (LLVMDataLocal x)
      , "="
      , "fdiv"
      , showLowTypeEmit t
      , showLLVMData d1 ++ ","
      , showLLVMData d2
      ]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMPrint t d) cont) = do
  fmt <- newNameWith "fmt"
  op1 <-
    emitOp $
    unwords
      [ showLLVMData (LLVMDataLocal fmt)
      , "="
      , "getelementptr [3 x i8], [3 x i8]* @fmt.i32, i32 0, i32 0"
      ]
  tmp <- newNameWith "tmp"
  op2 <-
    emitOp $
    unwords
      [ showLLVMData (LLVMDataLocal tmp)
      , "="
      , "call"
      , "i32 (i8*, ...)"
      , "@printf(i8* " ++ showLLVMData (LLVMDataLocal fmt) ++ ","
      , showLowTypeEmit t
      , showLLVMData d ++ ")"
      ]
  a <-
    emitLLVM funName $
    LLVMLet
      x
      (LLVMIntToPointer (LLVMDataLocal tmp) (LowTypeSignedInt 32) voidPtr)
      cont
  return $ op1 ++ op2 ++ a
emitLLVM _ LLVMUnreachable = emitOp $ unwords ["unreachable"]
emitLLVM funName c = do
  tmp <- newNameWith "result"
  emitLLVM funName $ LLVMLet tmp c $ LLVMReturn (LLVMDataLocal tmp)

emitOp :: String -> WithEnv [String]
emitOp s = return ["  " ++ s]

emitRet :: Identifier -> LLVMData -> WithEnv [String]
emitRet "main" d = do
  tmp <- newNameWith "cast"
  op1 <-
    emitOp $
    unwords
      [ showLLVMData (LLVMDataLocal tmp)
      , "="
      , "ptrtoint"
      , "i8*"
      , showLLVMData d
      , "to"
      , "i64"
      ]
  op2 <- emitOp $ unwords ["ret i64", showLLVMData (LLVMDataLocal tmp)]
  return $ op1 ++ op2
emitRet _ d = emitOp $ unwords ["ret i8*", showLLVMData d]

emitLabel :: String -> String
emitLabel s = s ++ ":"

constructLabelList :: [(Int, LLVM)] -> WithEnv [String]
constructLabelList [] = return []
constructLabelList ((_, _):rest) = do
  label <- newNameWith "case"
  labelList <- constructLabelList rest
  return $ label : labelList

showBranchList :: [(Int, String)] -> String
showBranchList xs = "[" ++ showItems (uncurry showBranch) xs ++ "]"

showBranch :: Int -> String -> String
showBranch i label =
  "i64 " ++ show i ++ ", label " ++ showLLVMData (LLVMDataLocal label)

showIndex :: [Int] -> String
showIndex [] = ""
showIndex [i] = "i32 " ++ show i
showIndex (i:is) = "i32 " ++ show i ++ ", " ++ showIndex is

showArg :: LLVMData -> String
showArg d = "i8* " ++ showLLVMData d

showArgs :: [LLVMData] -> String
showArgs ds = "(" ++ showItems showArg ds ++ ")"

showLowTypeEmit :: LowType -> String
showLowTypeEmit (LowTypeSignedInt i) = "i" ++ show i
-- LLVM doesn't distinguish unsigned integers from signed ones
showLowTypeEmit (LowTypeUnsignedInt i) = "i" ++ show i
showLowTypeEmit (LowTypeFloat 16) = "half"
showLowTypeEmit (LowTypeFloat 32) = "float"
showLowTypeEmit (LowTypeFloat 64) = "double"
showLowTypeEmit (LowTypeFloat i) = "f" ++ show i -- shouldn't occur
showLowTypeEmit (LowTypePointer t) = showLowTypeEmit t ++ "*"
showLowTypeEmit (LowTypeStruct ts) = "{" ++ showItems showLowTypeEmit ts ++ "}"
showLowTypeEmit (LowTypeFunction ts t) =
  showLowTypeEmit t ++ " (" ++ showItems showLowTypeEmit ts ++ ")"

showStruct :: Int -> String
showStruct i = "{" ++ showItems (const "i8*") [1 .. i] ++ "}"

-- for now
emitGlobal :: WithEnv [String]
emitGlobal =
  return
    [ "@fmt.i32 = constant [3 x i8] c\"%d\00\""
    , "declare i32 @printf(i8* noalias nocapture, ...)"
    , "declare i8* @malloc(i64)"
    , "declare void @free(i8*)"
    ]

showLLVMData :: LLVMData -> String
showLLVMData (LLVMDataLocal x) = "%" ++ x
showLLVMData (LLVMDataGlobal x) = "@" ++ x
showLLVMData (LLVMDataInt i _) = show i
showLLVMData (LLVMDataFloat x _) = show x
showLLVMData (LLVMDataStruct xs) = "{" ++ showItems showLLVMData xs ++ "}"
