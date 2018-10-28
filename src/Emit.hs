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
  xs <- forM (asmEnv env) $ uncurry emitDefinition
  return $ g ++ concat xs

emitDefinition :: Identifier -> ([Identifier], Asm) -> WithEnv [String]
emitDefinition name (args, asm) = do
  let prologue = sig name args ++ " {"
  content <- emitAsm name asm
  let epilogue = "}"
  return $ [prologue] ++ content ++ [epilogue]

sig :: Identifier -> [Identifier] -> String
sig "main" args = "define i64 @main" ++ showArgs (map AsmDataLocal args)
sig name args =
  "define i8* " ++ show (AsmDataGlobal name) ++ showArgs (map AsmDataLocal args)

emitBlock :: Identifier -> Identifier -> Asm -> WithEnv [String]
emitBlock funName name asm = do
  a <- emitAsm funName asm
  return $ emitLabel name : a

emitAsm :: Identifier -> Asm -> WithEnv [String]
emitAsm funName (AsmReturn d) = emitRet funName d
emitAsm funName (AsmGetElementPtr x base (i, n) cont) = do
  op <-
    emitOp $
    unwords
      [ show (AsmDataLocal x)
      , "= getelementptr"
      , showStruct n ++ ","
      , showStruct n ++ "*"
      , show base ++ ","
      , showIndex [0, i]
      ]
  xs <- emitAsm funName cont
  return $ op ++ xs
emitAsm funName (AsmCall x f args cont) = do
  op <-
    emitOp $
    unwords [show (AsmDataLocal x), "=", "call i8*", show f ++ showArgs args]
  a <- emitAsm funName cont
  return $ op ++ a
emitAsm funName (AsmCallTail f args) = do
  tmp <- newNameWith "tmp"
  op <-
    emitOp $
    unwords
      [show (AsmDataLocal tmp), "=", "tail call i8*", show f ++ showArgs args]
  a <- emitRet funName (AsmDataLocal tmp)
  return $ op ++ a
emitAsm funName (AsmBitcast x d fromType toType cont) = do
  op <-
    emitOp $
    unwords
      [ show (AsmDataLocal x)
      , "="
      , "bitcast"
      , showLowType fromType
      , show d
      , "to"
      , showLowType toType
      ]
  a <- emitAsm funName cont
  return $ op ++ a
emitAsm funName (AsmIntToPointer x d fromType toType cont) = do
  op <-
    emitOp $
    unwords
      [ show (AsmDataLocal x)
      , "="
      , "inttoptr"
      , showLowType fromType
      , show d
      , "to"
      , showLowType toType
      ]
  a <- emitAsm funName cont
  return $ op ++ a
emitAsm funName (AsmPointerToInt x d fromType toType cont) = do
  op <-
    emitOp $
    unwords
      [ show (AsmDataLocal x)
      , "="
      , "ptrtoint"
      , showLowType fromType
      , show d
      , "to"
      , showLowType toType
      ]
  a <- emitAsm funName cont
  return $ op ++ a
emitAsm funName (AsmSwitch d defaultBranch branchList) = do
  defaultLabel <- newNameWith "default"
  labelList <- constructLabelList branchList
  op <-
    emitOp $
    unwords
      [ "switch"
      , "i64"
      , show d ++ ","
      , "label"
      , show (AsmDataLocal defaultLabel)
      , showBranchList $ zip (map fst branchList) labelList
      ]
  let asmList = map snd branchList
  xs <-
    forM (zip labelList asmList ++ [(defaultLabel, defaultBranch)]) $
    uncurry (emitBlock funName)
  return $ op ++ concat xs
emitAsm funName (AsmLoad x d cont) = do
  op <- emitOp $ unwords [show (AsmDataLocal x), "=", "load i8*, i8**", show d]
  a <- emitAsm funName cont
  return $ op ++ a
emitAsm funName (AsmStore (d1, t1) (d2, t2) cont) = do
  op <-
    emitOp $
    unwords ["store", showLowType t1, show d1 ++ ",", showLowType t2, show d2]
  a <- emitAsm funName cont
  return $ op ++ a
emitAsm funName (AsmAlloc x ts cont) = do
  size <- newNameWith "sizeptr"
  op1 <-
    emitOp $
    unwords
      [ show (AsmDataLocal size)
      , "="
      , "getelementptr i64, i64* null, i32 " ++ show (length ts)
      ]
  casted <- newNameWith "size"
  op2 <-
    emitOp $
    unwords
      [ show (AsmDataLocal casted)
      , "="
      , "ptrtoint i64*"
      , show (AsmDataLocal size)
      , "to i64"
      ]
  op3 <-
    emitOp $
    unwords
      [ show (AsmDataLocal x)
      , "="
      , "call"
      , "i8*"
      , "@malloc(i64 " ++ show (AsmDataLocal casted) ++ ")"
      ]
  a <- emitAsm funName cont
  return $ op1 ++ op2 ++ op3 ++ a
emitAsm funName (AsmFree d cont) = do
  op <- emitOp $ unwords ["call", "void", "@free(i8* " ++ show d ++ ")"]
  a <- emitAsm funName cont
  return $ op ++ a
emitAsm funName (AsmArith x (ArithAdd, t) d1 d2 cont)
  | t `elem` intLowTypeList
  -- thanks to the two's complement representation of LLVM, these arithmetic
  -- instructions ('add', 'sub', 'mul') are valid for both signed and unsigned integers.
   = do
    op <-
      emitOp $
      unwords
        [ show (AsmDataLocal x)
        , "="
        , "add"
        , showLowType t
        , show d1 ++ ","
        , show d2
        ]
    a <- emitAsm funName cont
    return $ op ++ a
emitAsm funName (AsmArith x (ArithAdd, t) d1 d2 cont) = do
  op <-
    emitOp $
    unwords
      [ show (AsmDataLocal x)
      , "="
      , "fadd"
      , showLowType t
      , show d1 ++ ","
      , show d2
      ]
  a <- emitAsm funName cont
  return $ op ++ a
emitAsm funName (AsmArith x (ArithSub, t) d1 d2 cont)
  | t `elem` intLowTypeList = do
    op <-
      emitOp $
      unwords
        [ show (AsmDataLocal x)
        , "="
        , "sub"
        , showLowType t
        , show d1 ++ ","
        , show d2
        ]
    a <- emitAsm funName cont
    return $ op ++ a
emitAsm funName (AsmArith x (ArithSub, t) d1 d2 cont) = do
  op <-
    emitOp $
    unwords
      [ show (AsmDataLocal x)
      , "="
      , "fsub"
      , showLowType t
      , show d1 ++ ","
      , show d2
      ]
  a <- emitAsm funName cont
  return $ op ++ a
emitAsm funName (AsmArith x (ArithMul, t) d1 d2 cont)
  | t `elem` intLowTypeList = do
    op <-
      emitOp $
      unwords
        [ show (AsmDataLocal x)
        , "="
        , "mul"
        , showLowType t
        , show d1 ++ ","
        , show d2
        ]
    a <- emitAsm funName cont
    return $ op ++ a
emitAsm funName (AsmArith x (ArithMul, t) d1 d2 cont) = do
  op <-
    emitOp $
    unwords
      [ show (AsmDataLocal x)
      , "="
      , "fmul"
      , showLowType t
      , show d1 ++ ","
      , show d2
      ]
  a <- emitAsm funName cont
  return $ op ++ a
emitAsm funName (AsmArith x (ArithDiv, t@(LowTypeSignedInt _)) d1 d2 cont) = do
  op <-
    emitOp $
    unwords
      [ show (AsmDataLocal x)
      , "="
      , "sdiv"
      , showLowType t
      , show d1 ++ ","
      , show d2
      ]
  a <- emitAsm funName cont
  return $ op ++ a
emitAsm funName (AsmArith x (ArithDiv, t@(LowTypeUnsignedInt _)) d1 d2 cont) = do
  op <-
    emitOp $
    unwords
      [ show (AsmDataLocal x)
      , "="
      , "udiv"
      , showLowType t
      , show d1 ++ ","
      , show d2
      ]
  a <- emitAsm funName cont
  return $ op ++ a
emitAsm funName (AsmArith x (ArithDiv, t) d1 d2 cont) = do
  op <-
    emitOp $
    unwords
      [ show (AsmDataLocal x)
      , "="
      , "fdiv"
      , showLowType t
      , show d1 ++ ","
      , show d2
      ]
  a <- emitAsm funName cont
  return $ op ++ a
emitAsm funName (AsmPrint t d cont) = do
  fmt <- newNameWith "fmt"
  op1 <-
    emitOp $
    unwords
      [ show (AsmDataLocal fmt)
      , "="
      , "getelementptr [3 x i8], [3 x i8]* @fmt.i32, i32 0, i32 0"
      ]
  op2 <-
    emitOp $
    unwords
      [ "call"
      , "i32 (i8*, ...)"
      , "@printf(i8* " ++ show (AsmDataLocal fmt) ++ ","
      , showLowType t
      , show d ++ ")"
      ]
  a <- emitAsm funName cont
  return $ op1 ++ op2 ++ a

emitOp :: String -> WithEnv [String]
emitOp s = return ["  " ++ s]

emitRet :: Identifier -> AsmData -> WithEnv [String]
emitRet "main" d = do
  tmp <- newNameWith "cast"
  op1 <-
    emitOp $
    unwords
      [show (AsmDataLocal tmp), "=", "ptrtoint", "i8*", show d, "to", "i64"]
  op2 <- emitOp $ unwords ["ret i64", show (AsmDataLocal tmp)]
  return $ op1 ++ op2
emitRet _ d = emitOp $ unwords ["ret i8*", show d]

emitLabel :: String -> String
emitLabel s = s ++ ":"

constructLabelList :: [(Int, Asm)] -> WithEnv [String]
constructLabelList [] = return []
constructLabelList ((_, _):rest) = do
  label <- newNameWith "case"
  labelList <- constructLabelList rest
  return $ label : labelList

showBranchList :: [(Int, String)] -> String
showBranchList xs = "[" ++ showItems (uncurry showBranch) xs ++ "]"

showBranch :: Int -> String -> String
showBranch i label = "i64 " ++ show i ++ ", label " ++ show (AsmDataLocal label)

showIndex :: [Int] -> String
showIndex [] = ""
showIndex [i] = "i32 " ++ show i
showIndex (i:is) = "i32 " ++ show i ++ ", " ++ showIndex is

showArg :: AsmData -> String
showArg d = "i8* " ++ show d

showArgs :: [AsmData] -> String
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
