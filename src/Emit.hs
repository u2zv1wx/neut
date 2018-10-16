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
  let name' = DataLabel name
  let args' = map DataLocal args
  liftIO $ putStrLn $ "define i8* " ++ showData name' ++ showArgs args' ++ "{"
  emitAsm asm
  liftIO $ putStrLn "}"

emitBlock :: Identifier -> Asm -> WithEnv ()
emitBlock name asm = do
  emitLabel name
  emitAsm asm

emitAsm :: Asm -> WithEnv ()
emitAsm (_ :< AsmReturn d) = emitOp $ unwords ["ret i8*", showData d]
emitAsm (_ :< AsmGetElementPtr x base (i, n) cont) = do
  emitOp $
    unwords
      [ showData (DataLocal x)
      , "= getelementptr"
      , showStructOfLength n ++ ","
      , showStructOfLength n ++ "*"
      , showData base ++ ","
      , showIndex [0, i]
      ]
  emitAsm cont
emitAsm (_ :< AsmCall x f args cont) = do
  emitOp $
    unwords
      [showData (DataLocal x), "=", "i8* call", showData f ++ showArgs args]
  emitAsm cont
emitAsm (_ :< AsmCallTail f args) = do
  tmp <- newNameWith "tmp"
  emitOp $
    unwords
      [ showData (DataLocal tmp)
      , "="
      , "tail call i8*"
      , showData f ++ showArgs args
      ]
  emitOp $ unwords ["ret i8*", showData (DataLocal tmp)]
emitAsm (_ :< AsmBitcast x d fromType toType cont) = do
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
emitAsm (_ :< AsmIntToPointer x d fromType _ cont) = do
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
emitAsm (_ :< AsmPointerToInt x d _ toType cont) = do
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
emitAsm (_ :< AsmSwitch d defaultBranch branchList) = do
  defaultLabel <- newNameWith "default"
  labelList <- constructLabelList branchList
  emitOp $
    unwords
      [ "switch"
      , "i32"
      , showData d ++ ","
      , "label"
      , defaultLabel
      , showBranchList $ zip (map fst branchList) labelList
      ]
  let asmList = map snd branchList
  forM_ ((defaultLabel, defaultBranch) : zip labelList asmList) $
    uncurry emitBlock
emitAsm (_ :< AsmFree d cont) = do
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
constructLabelList ((i, _):rest) = do
  label <- newNameWith $ "case." ++ show i
  labelList <- constructLabelList rest
  return $ label : labelList

showBranchList :: [(Int, String)] -> String
showBranchList xs = "[" ++ showList (uncurry showBranch) xs ++ "]"

showBranch :: Int -> String -> String
showBranch i label =
  "i32 " ++ show i ++ ", label " ++ showData (DataLocal label)

showData :: Data -> String
showData (DataLocal x) = "%" ++ x
showData (DataLabel x) = "@" ++ x
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
showLowType = undefined

showStructOfLength :: Int -> String
showStructOfLength i = "{" ++ showList (const "i8*") [1 .. i] ++ "}"

showList :: (a -> String) -> [a] -> String
showList _ [] = ""
showList f [a] = f a
showList f (a:as) = f a ++ ", " ++ showList f as
