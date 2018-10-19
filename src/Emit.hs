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
  let name' = AsmDataGlobal name
  let args' = map AsmDataLocal args
  liftIO $
    putStrLn $ "define i8* " ++ showAsmData name' ++ showArgs args' ++ " {"
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
      [ showAsmData (AsmDataLocal x)
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
      [ showAsmData (AsmDataLocal x)
      , "="
      , "i8* call"
      , showAsmData f ++ showArgs args
      ]
  emitAsm cont
emitAsm (AsmCallTail f args) = do
  tmp <- newNameWith "tmp"
  emitOp $
    unwords
      [ showAsmData (AsmDataLocal tmp)
      , "="
      , "tail call i8*"
      , showAsmData f ++ showArgs args
      ]
  emitOp $ unwords ["ret i8*", showAsmData (AsmDataLocal tmp)]
emitAsm (AsmBitcast x d fromType toType cont) = do
  emitOp $
    unwords
      [ showAsmData (AsmDataLocal x)
      , "="
      , "bitcast"
      , showLowType fromType
      , showAsmData d
      , "to"
      , showLowType toType
      ]
  emitAsm cont
emitAsm (AsmIntToPointer x d fromType _ cont) = do
  emitOp $
    unwords
      [ showAsmData (AsmDataLocal x)
      , "="
      , "inttoptr"
      , showLowType fromType
      , showAsmData d
      , "to i8*"
      ]
  emitAsm cont
emitAsm (AsmPointerToInt x d _ toType cont) = do
  emitOp $
    unwords
      [ showAsmData (AsmDataLocal x)
      , "="
      , "ptrtoint"
      , "i8*"
      , showAsmData d
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
      , showAsmData d ++ ","
      , "label"
      , showAsmData (AsmDataLocal defaultLabel)
      , showBranchList $ zip (map fst branchList) labelList
      ]
  let asmList = map snd branchList
  forM_ (zip labelList asmList ++ [(defaultLabel, defaultBranch)]) $
    uncurry emitBlock
emitAsm (AsmLoad x d cont) = do
  emitOp $
    unwords [showAsmData (AsmDataLocal x), "=", "load", "i8*", showAsmData d]
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
      [ showAsmData (AsmDataLocal size)
      , "="
      , "getelementptr i64, i64* null, i32 " ++ show (length ts)
      ]
  casted <- newNameWith "size"
  emitOp $
    unwords
      [ showAsmData (AsmDataLocal casted)
      , "="
      , "ptrtoint i64*"
      , showAsmData (AsmDataLocal size)
      , "to i32"
      ]
  emitOp $
    unwords
      [ showAsmData (AsmDataLocal x)
      , "="
      , "call"
      , "i8*"
      , "@malloc(i32 " ++ showAsmData (AsmDataLocal casted) ++ ")"
      ]
  emitAsm cont
emitAsm (AsmFree d cont) = do
  emitOp $ unwords ["call", "void", "@free(i8* " ++ showAsmData d ++ ")"]
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
  "i32 " ++ show i ++ ", label " ++ showAsmData (AsmDataLocal label)

showAsmData :: AsmData -> String
showAsmData (AsmDataLocal x) = "%" ++ x
showAsmData (AsmDataGlobal x) = "@" ++ x
showAsmData (AsmDataInt32 i) = show i

showIndex :: [Int] -> String
showIndex [] = ""
showIndex [i] = "i32 " ++ show i
showIndex (i:is) = "i32 " ++ show i ++ ", " ++ showIndex is

showArg :: AsmData -> String
showArg d = "i8* " ++ showAsmData d

showArgs :: [AsmData] -> String
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
