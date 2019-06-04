-- Just emit the resulting LLVM code.
-- The result is [String], where each element corresponds to a line.
module Emit
  ( emit
  ) where

import Prelude hiding (showList)

import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans.Except
import Data.IORef

import Data

import Control.Comonad.Cofree

import qualified Text.Show.Pretty as Pr

import Data.List

import Debug.Trace

emit :: WithEnv [String]
emit = do
  env <- get
  g <- emitGlobal
  xs <- forM (llvmEnv env) $ uncurry emitDefinition
  return $ g ++ concat xs

emitDefinition :: Identifier -> ([Identifier], LLVM) -> WithEnv [String]
emitDefinition name (args, asm) = do
  let prologue = sig name args ++ " {"
  content <- emitLLVM name asm
  let epilogue = "}"
  return $ [prologue] ++ content ++ [epilogue]

sig :: Identifier -> [Identifier] -> String
sig "main" args = "define i64 @main" ++ showArgs (map LLVMDataLocal args)
sig name args =
  "define i8* " ++
  show (LLVMDataGlobal name) ++ showArgs (map LLVMDataLocal args)

emitBlock :: Identifier -> Identifier -> LLVM -> WithEnv [String]
emitBlock funName name asm = do
  a <- emitLLVM funName asm
  return $ emitLabel name : a

emitLLVM :: Identifier -> LLVM -> WithEnv [String]
emitLLVM funName (LLVMCall f args) = do
  tmp <- newNameWith "tmp"
  op <-
    emitOp $
    unwords
      [show (LLVMDataLocal tmp), "=", "tail call i8*", show f ++ showArgs args]
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
      , show d ++ ","
      , "label"
      , show (LLVMDataLocal defaultLabel)
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
    unwords [show (LLVMDataLocal x), "=", "call i8*", show f ++ showArgs args]
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
      [ show (LLVMDataLocal x)
      , "= getelementptr"
      , showStruct n ++ ","
      , showStruct n ++ "*"
      , show base ++ ","
      , showIndex [0, i]
      ]
  xs <- emitLLVM funName cont
  return $ op ++ xs
emitLLVM funName (LLVMLet x (LLVMBitcast d fromType toType) cont) = do
  op <-
    emitOp $
    unwords
      [ show (LLVMDataLocal x)
      , "="
      , "bitcast"
      , showLowType fromType
      , show d
      , "to"
      , showLowType toType
      ]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMIntToPointer d fromType toType) cont) = do
  op <-
    emitOp $
    unwords
      [ show (LLVMDataLocal x)
      , "="
      , "inttoptr"
      , showLowType fromType
      , show d
      , "to"
      , showLowType toType
      ]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMPointerToInt d fromType toType) cont) = do
  op <-
    emitOp $
    unwords
      [ show (LLVMDataLocal x)
      , "="
      , "ptrtoint"
      , showLowType fromType
      , show d
      , "to"
      , showLowType toType
      ]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMLoad d) cont) = do
  op <- emitOp $ unwords [show (LLVMDataLocal x), "=", "load i8*, i8**", show d]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet _ (LLVMStore (d1, t1) (d2, t2)) cont) = do
  op <-
    emitOp $
    unwords ["store", showLowType t1, show d1 ++ ",", showLowType t2, show d2]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMAlloc ts) cont) = do
  size <- newNameWith "sizeptr"
  op1 <-
    emitOp $
    unwords
      [ show (LLVMDataLocal size)
      , "="
      , "getelementptr i64, i64* null, i32 " ++ show (length ts)
      ]
  casted <- newNameWith "size"
  op2 <-
    emitOp $
    unwords
      [ show (LLVMDataLocal casted)
      , "="
      , "ptrtoint i64*"
      , show (LLVMDataLocal size)
      , "to i64"
      ]
  op3 <-
    emitOp $
    unwords
      [ show (LLVMDataLocal x)
      , "="
      , "call"
      , "i8*"
      , "@malloc(i64 " ++ show (LLVMDataLocal casted) ++ ")"
      ]
  a <- emitLLVM funName cont
  return $ op1 ++ op2 ++ op3 ++ a
emitLLVM funName (LLVMLet _ (LLVMFree d) cont) = do
  op <- emitOp $ unwords ["call", "void", "@free(i8* " ++ show d ++ ")"]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMArith (ArithAdd, t) d1 d2) cont)
  | t `elem` intLowTypeList
  -- thanks to the two's complement representation of LLVM, these arithmetic
  -- instructions ('add', 'sub', 'mul') are valid for both signed and unsigned integers.
   = do
    op <-
      emitOp $
      unwords
        [ show (LLVMDataLocal x)
        , "="
        , "add"
        , showLowType t
        , show d1 ++ ","
        , show d2
        ]
    a <- emitLLVM funName cont
    return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMArith (ArithAdd, t) d1 d2) cont) = do
  op <-
    emitOp $
    unwords
      [ show (LLVMDataLocal x)
      , "="
      , "fadd"
      , showLowType t
      , show d1 ++ ","
      , show d2
      ]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMArith (ArithSub, t) d1 d2) cont)
  | t `elem` intLowTypeList = do
    op <-
      emitOp $
      unwords
        [ show (LLVMDataLocal x)
        , "="
        , "sub"
        , showLowType t
        , show d1 ++ ","
        , show d2
        ]
    a <- emitLLVM funName cont
    return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMArith (ArithSub, t) d1 d2) cont) = do
  op <-
    emitOp $
    unwords
      [ show (LLVMDataLocal x)
      , "="
      , "fsub"
      , showLowType t
      , show d1 ++ ","
      , show d2
      ]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMArith (ArithMul, t) d1 d2) cont)
  | t `elem` intLowTypeList = do
    op <-
      emitOp $
      unwords
        [ show (LLVMDataLocal x)
        , "="
        , "mul"
        , showLowType t
        , show d1 ++ ","
        , show d2
        ]
    a <- emitLLVM funName cont
    return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMArith (ArithMul, t) d1 d2) cont) = do
  op <-
    emitOp $
    unwords
      [ show (LLVMDataLocal x)
      , "="
      , "fmul"
      , showLowType t
      , show d1 ++ ","
      , show d2
      ]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMArith (ArithDiv, t@(LowTypeSignedInt _)) d1 d2) cont) = do
  op <-
    emitOp $
    unwords
      [ show (LLVMDataLocal x)
      , "="
      , "sdiv"
      , showLowType t
      , show d1 ++ ","
      , show d2
      ]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMArith (ArithDiv, t@(LowTypeUnsignedInt _)) d1 d2) cont) = do
  op <-
    emitOp $
    unwords
      [ show (LLVMDataLocal x)
      , "="
      , "udiv"
      , showLowType t
      , show d1 ++ ","
      , show d2
      ]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet x (LLVMArith (ArithDiv, t) d1 d2) cont) = do
  op <-
    emitOp $
    unwords
      [ show (LLVMDataLocal x)
      , "="
      , "fdiv"
      , showLowType t
      , show d1 ++ ","
      , show d2
      ]
  a <- emitLLVM funName cont
  return $ op ++ a
emitLLVM funName (LLVMLet _ (LLVMPrint t d) cont) = do
  fmt <- newNameWith "fmt"
  op1 <-
    emitOp $
    unwords
      [ show (LLVMDataLocal fmt)
      , "="
      , "getelementptr [3 x i8], [3 x i8]* @fmt.i32, i32 0, i32 0"
      ]
  op2 <-
    emitOp $
    unwords
      [ "call"
      , "i32 (i8*, ...)"
      , "@printf(i8* " ++ show (LLVMDataLocal fmt) ++ ","
      , showLowType t
      , show d ++ ")"
      ]
  a <- emitLLVM funName cont
  return $ op1 ++ op2 ++ a
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
      [show (LLVMDataLocal tmp), "=", "ptrtoint", "i8*", show d, "to", "i64"]
  op2 <- emitOp $ unwords ["ret i64", show (LLVMDataLocal tmp)]
  return $ op1 ++ op2
emitRet _ d = emitOp $ unwords ["ret i8*", show d]

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
  "i64 " ++ show i ++ ", label " ++ show (LLVMDataLocal label)

showIndex :: [Int] -> String
showIndex [] = ""
showIndex [i] = "i32 " ++ show i
showIndex (i:is) = "i32 " ++ show i ++ ", " ++ showIndex is

showArg :: LLVMData -> String
showArg d = "i8* " ++ show d

showArgs :: [LLVMData] -> String
showArgs ds = "(" ++ showItems showArg ds ++ ")"

showLowType :: LowType -> String
showLowType (LowTypeSignedInt i) = "i" ++ show i
-- LLVM doesn't distinguish unsigned integers from signed ones
showLowType (LowTypeUnsignedInt i) = "i" ++ show i
showLowType (LowTypeFloat 16) = "half"
showLowType (LowTypeFloat 32) = "float"
showLowType (LowTypeFloat 64) = "double"
showLowType (LowTypeFloat i) = "f" ++ show i -- shouldn't occur
showLowType (LowTypePointer t) = showLowType t ++ "*"
showLowType (LowTypeStruct ts) = "{" ++ showList ts ++ "}"
showLowType (LowTypeArray i t) = "[" ++ show i ++ " x " ++ showLowType t ++ "]"
showLowType (LowTypeFunction ts t) = showLowType t ++ " (" ++ showList ts ++ ")"

showStruct :: Int -> String
showStruct i = "{" ++ showItems (const "i8*") [1 .. i] ++ "}"

showItems :: (a -> String) -> [a] -> String
showItems _ [] = ""
showItems f [a] = f a
showItems f (a:as) = f a ++ ", " ++ showItems f as

-- for now
emitGlobal :: WithEnv [String]
emitGlobal =
  return
    [ "@fmt.i32 = constant [3 x i8] c\"%d\00\""
    , "declare i32 @printf(i8* noalias nocapture, ...)"
    , "declare i8* @malloc(i64)"
    , "declare void @free(i8*)"
    ]
