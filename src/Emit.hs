module Emit
  ( emit
  , emitGlobalLabel
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

emit :: WithEnv ()
emit = do
  env <- get
  emitGlobal
  forM_ (asmEnv env) $ uncurry emitDefinition

emitDefinition :: Identifier -> ([Identifier], Asm) -> WithEnv ()
emitDefinition name (args, asm) = do
  liftIO $ putStrLn $ sig name args ++ " {"
  emitAsm name asm
  liftIO $ putStrLn "}"

sig :: Identifier -> [Identifier] -> String
sig "main" args = "define i64 @main" ++ showArgs (map AsmDataLocal args)
sig name args =
  "define i8* " ++ show (AsmDataGlobal name) ++ showArgs (map AsmDataLocal args)

emitBlock :: Identifier -> Identifier -> Asm -> WithEnv ()
emitBlock funName name asm = do
  emitLabel name
  emitAsm funName asm

emitAsm :: Identifier -> Asm -> WithEnv ()
emitAsm funName (AsmReturn d) = emitRet funName d
emitAsm funName (AsmGetElementPtr x base (i, n) cont) = do
  emitOp $
    unwords
      [ show (AsmDataLocal x)
      , "= getelementptr"
      , showStructOfLength n ++ ","
      , showStructOfLength n ++ "*"
      , show base ++ ","
      , showIndex [0, i]
      ]
  emitAsm funName cont
emitAsm funName (AsmCall x f args cont) = do
  emitOp $
    unwords [show (AsmDataLocal x), "=", "call i8*", show f ++ showArgs args]
  emitAsm funName cont
emitAsm funName (AsmCallTail f args) = do
  tmp <- newNameWith "tmp"
  emitOp $
    unwords
      [show (AsmDataLocal tmp), "=", "tail call i8*", show f ++ showArgs args]
  emitRet funName (AsmDataLocal tmp)
  -- emitOp $ unwords ["ret i8*", show (AsmDataLocal tmp)]
emitAsm funName (AsmBitcast x d fromType toType cont) = do
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
  emitAsm funName cont
emitAsm funName (AsmIntToPointer x d fromType toType cont) = do
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
  emitAsm funName cont
emitAsm funName (AsmPointerToInt x d fromType toType cont) = do
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
  emitAsm funName cont
emitAsm funName (AsmSwitch d defaultBranch branchList) = do
  defaultLabel <- newNameWith "default"
  labelList <- constructLabelList branchList
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
  forM_ (zip labelList asmList ++ [(defaultLabel, defaultBranch)]) $
    uncurry (emitBlock funName)
emitAsm funName (AsmLoad x d cont) = do
  emitOp $ unwords [show (AsmDataLocal x), "=", "load i8*, i8**", show d]
  emitAsm funName cont
emitAsm funName (AsmStore (d1, t1) (d2, t2) cont) = do
  emitOp $
    unwords ["store", showLowType t1, show d1 ++ ",", showLowType t2, show d2]
  emitAsm funName cont
emitAsm funName (AsmAlloc x ts cont) = do
  size <- newNameWith "sizeptr"
  emitOp $
    unwords
      [ show (AsmDataLocal size)
      , "="
      , "getelementptr i64, i64* null, i32 " ++ show (length ts)
      ]
  casted <- newNameWith "size"
  emitOp $
    unwords
      [ show (AsmDataLocal casted)
      , "="
      , "ptrtoint i64*"
      , show (AsmDataLocal size)
      , "to i64"
      ]
  emitOp $
    unwords
      [ show (AsmDataLocal x)
      , "="
      , "call"
      , "i8*"
      , "@malloc(i64 " ++ show (AsmDataLocal casted) ++ ")"
      ]
  emitAsm funName cont
emitAsm funName (AsmFree d cont) = do
  emitOp $ unwords ["call", "void", "@free(i8* " ++ show d ++ ")"]
  emitAsm funName cont
emitAsm funName (AsmArith x (ArithAdd, t) d1 d2 cont) = do
  emitOp $
    unwords
      [ show (AsmDataLocal x)
      , "="
      , "add"
      , showLowType t
      , show d1 ++ ","
      , show d2
      ]
  emitAsm funName cont
emitAsm funName (AsmArith x (ArithSub, t) d1 d2 cont) = do
  emitOp $
    unwords
      [ show (AsmDataLocal x)
      , "="
      , "sub"
      , showLowType t
      , show d1 ++ ","
      , show d2
      ]
  emitAsm funName cont
emitAsm funName (AsmArith x (ArithMul, t) d1 d2 cont) = do
  emitOp $
    unwords
      [ show (AsmDataLocal x)
      , "="
      , "mul"
      , showLowType t
      , show d1 ++ ","
      , show d2
      ]
  emitAsm funName cont
emitAsm funName (AsmPrint t d cont) = do
  fmt <- newNameWith "fmt"
  emitOp $
    unwords
      [ show (AsmDataLocal fmt)
      , "="
      , "getelementptr [3 x i8], [3 x i8]* @fmt.i32, i32 0, i32 0"
      ]
  -- emitOp $ unwords [show (AsmDataLocal fmt), "=", "getelementptr"]
  emitOp $
    unwords
      [ "call"
      , "i32 (i8*, ...)"
      , "@printf(i8* " ++ show (AsmDataLocal fmt) ++ ","
      , showLowType t
      , show d ++ ")"
      ]
  emitAsm funName cont

emitOp :: String -> WithEnv ()
emitOp s = liftIO $ putStrLn $ "  " ++ s

emitGlobalLabel :: Identifier -> WithEnv ()
emitGlobalLabel label = liftIO $ putStrLn $ "  " ++ ".globl " ++ label

emitRet :: Identifier -> AsmData -> WithEnv ()
emitRet "main" d = do
  tmp <- newNameWith "cast"
  emitOp $
    unwords
      [show (AsmDataLocal tmp), "=", "ptrtoint", "i8*", show d, "to", "i64"]
  emitOp $ unwords ["ret i64", show (AsmDataLocal tmp)]
emitRet _ d = emitOp $ unwords ["ret i8*", show d]

emitLabel :: String -> WithEnv ()
emitLabel s = liftIO $ putStrLn $ s ++ ":"

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
showLowType (LowTypeInt i) = "i" ++ show i
showLowType (LowTypePointer t) = showLowType t ++ "*"
showLowType (LowTypeStruct ts) = "{" ++ showList ts ++ "}"
showLowType (LowTypeArray i t) = "[" ++ show i ++ " x " ++ showLowType t ++ "]"
showLowType (LowTypeFunction ts t) = showLowType t ++ " (" ++ showList ts ++ ")"

showStructOfLength :: Int -> String
showStructOfLength i = "{" ++ showItems (const "i8*") [1 .. i] ++ "}"

showItems :: (a -> String) -> [a] -> String
showItems _ [] = ""
showItems f [a] = f a
showItems f (a:as) = f a ++ ", " ++ showItems f as

-- for now
emitGlobal :: WithEnv ()
emitGlobal = do
  liftIO $ putStrLn "@fmt.i32 = constant [3 x i8] c\"%d\00\""
  liftIO $ putStrLn "declare i32 @printf(i8* noalias nocapture, ...)"
  liftIO $ putStrLn "declare i8* @malloc(i64)"
  liftIO $ putStrLn "declare void @free(i8*)"
