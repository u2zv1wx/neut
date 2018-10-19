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
  forM_ (asmEnv env) $ uncurry emitDefinition

emitDefinition :: Identifier -> ([Identifier], Asm) -> WithEnv ()
emitDefinition name (args, asm) = do
  let name' = DataGlobal name
  let args' = map DataLocal args
  liftIO $ putStrLn $ "define i8* " ++ showData name' ++ showArgs args' ++ " {"
  emitAsm asm
  liftIO $ putStrLn "}"

emitBlock :: Identifier -> Asm -> WithEnv ()
emitBlock name asm = do
  emitLabel name
  emitAsm asm

emitAsm :: Asm -> WithEnv ()
emitAsm (AsmReturn d) = emitOp $ unwords ["ret i8*", showAsmData d]
emitAsm (AsmGetElementPtr x base (i, n) cont) = do
  emitOp $
    unwords
      [ showData (DataLocal x)
      , "= getelementptr"
      , showStructOfLength n ++ ","
      , showStructOfLength n ++ "*"
      , showAsmData base ++ ","
      , showIndex [0, i, 0]
      ]
  emitAsm cont
emitAsm (AsmCall x f args cont) = do
  emitOp $
    unwords
      [showData (DataLocal x), "=", "i8* call", showData f ++ showArgs args]
  emitAsm cont
emitAsm (AsmCallTail f args) = do
  tmp <- newNameWith "tmp"
  emitOp $
    unwords
      [ showData (DataLocal tmp)
      , "="
      , "tail call i8*"
      , showData f ++ showArgs args
      ]
  emitOp $ unwords ["ret i8*", showData (DataLocal tmp)]
emitAsm (AsmBitcast x d fromType toType cont) = do
  emitOp $
    unwords
      [ showData (DataLocal x)
      , "="
      , "bitcast"
      , showLowType fromType
      , showData d
      , "to"
      , showLowType toType
      ]
  emitAsm cont
emitAsm (AsmIntToPointer x d fromType _ cont) = do
  emitOp $
    unwords
      [ showData (DataLocal x)
      , "="
      , "inttoptr"
      , showLowType fromType
      , showData d
      , "to i8*"
      ]
  emitAsm cont
emitAsm (AsmPointerToInt x d _ toType cont) = do
  emitOp $
    unwords
      [ showData (DataLocal x)
      , "="
      , "ptrtoint"
      , "i8*"
      , showData d
      , "to"
      , showLowType toType
      ]
  emitAsm cont
emitAsm (AsmSwitch d defaultBranch branchList) = do
  defaultLabel <- newNameWith "default"
  labelList <- constructLabelList branchList
  emitOp $
    unwords
      [ "switch"
      , "i32"
      , showData d ++ ","
      , "label"
      , showData (DataLocal defaultLabel)
      , showBranchList $ zip (map fst branchList) labelList
      ]
  let asmList = map snd branchList
  forM_ (zip labelList asmList ++ [(defaultLabel, defaultBranch)]) $
    uncurry emitBlock
emitAsm (AsmLoad x d cont) = do
  emitOp $ unwords [showData (DataLocal x), "=", "load", "i8*", showAsmData d]
  emitAsm cont
emitAsm (AsmStore (d1, t1) (d2, t2) cont) = do
  emitOp $
    unwords
      [ "store"
      , showLowType t1
      , showAsmData d1 ++ ","
      , showLowType t2
      , showAsmData d2
      ]
  emitAsm cont
emitAsm (AsmAlloc x ts cont) = do
  size <- newNameWith "sizeptr"
  emitOp $
    unwords
      [ showData (DataLocal size)
      , "="
      , "getelementptr i64, i64* null, i32 " ++ show (length ts)
      ]
  casted <- newNameWith "size"
  emitOp $
    unwords
      [ showData (DataLocal casted)
      , "="
      , "ptrtoint i64*"
      , showData (DataLocal size)
      , "to i32"
      ]
  emitOp $
    unwords
      [ showData (DataLocal x)
      , "="
      , "call"
      , "i8*"
      , "@malloc(i32 " ++ showData (DataLocal casted) ++ ")"
      ]
  emitAsm cont
emitAsm (AsmFree d cont) = do
  emitOp $ unwords ["call", "void", "@free(i8* " ++ showData d ++ ")"]
  emitAsm cont

emitOp :: String -> WithEnv ()
emitOp s = liftIO $ putStrLn $ "  " ++ s

emitGlobalLabel :: Identifier -> WithEnv ()
emitGlobalLabel label = liftIO $ putStrLn $ "  " ++ ".globl " ++ label

emitLabel :: String -> WithEnv ()
emitLabel s = liftIO $ putStrLn $ s ++ ":"

constructLabelList :: [(Int, Asm)] -> WithEnv [String]
constructLabelList [] = return []
constructLabelList ((_, _):rest) = do
  label <- newNameWith "case"
  labelList <- constructLabelList rest
  return $ label : labelList

showBranchList :: [(Int, String)] -> String
showBranchList xs = "[" ++ showList (uncurry showBranch) xs ++ "]"

showBranch :: Int -> String -> String
showBranch i label =
  "i32 " ++ show i ++ ", label " ++ showData (DataLocal label)

showAsmData :: AsmData -> String
showAsmData (AsmDataLocal x) = "%" ++ x
showAsmData (AsmDataGlobal x) = "@" ++ x
showAsmData (AsmDataInt32 i) = show i

showData :: Data -> String
showData (DataLocal x) = "%" ++ x
showData (DataGlobal x) = "@" ++ x
showData (DataInt32 i) = show i
showData (DataStruct ds) = "{" ++ showList showData ds ++ "}*"

showIndex :: [Int] -> String
showIndex [] = ""
showIndex [i] = "i32 " ++ show i
showIndex (i:is) = "i32 " ++ show i ++ ", " ++ showIndex is

showArg :: Data -> String
showArg d = "i8* " ++ showData d

showArgs :: [Data] -> String
showArgs ds = "(" ++ showList showArg ds ++ ")"

showLowType :: LowType -> String
showLowType (LowTypeInt i) = "i" ++ show i
showLowType (LowTypePointer t) = showLowType t ++ "*"
showLowType (LowTypeStruct ts) = "{" ++ showList showLowType ts ++ "}"

showStructOfLength :: Int -> String
showStructOfLength i = "{" ++ showList (const "i8*") [1 .. i] ++ "}"

showList :: (a -> String) -> [a] -> String
showList _ [] = ""
showList f [a] = f a
showList f (a:as) = f a ++ ", " ++ showList f as
