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
  ts <- mapM lookupValueTypeEnv' args
  let args' = map (\(a, t) -> (DataLocal a, t)) $ zip args ts
  liftIO $ putStrLn $ "define i64 " ++ showData name' ++ showArgs args' ++ "{"
  emitAsm asm
  liftIO $ putStrLn "}"

emitBlock :: Identifier -> Asm -> WithEnv ()
emitBlock name asm = do
  emitLabel name
  emitAsm asm

emitAsm :: Asm -> WithEnv ()
emitAsm (_ :< AsmReturn (d, t)) =
  emitOp $ unwords ["ret", showType t, showData d]
emitAsm (_ :< AsmGetElementPtr x (base, t) i cont) = do
  emitOp $
    unwords
      [ x
      , "= getelementptr"
      , showTypeNoPtr t ++ ","
      , showType t
      , showData base ++ ","
      , showIndex [0, i]
      ]
  emitAsm cont
emitAsm (_ :< AsmCall x (f, _) args cont) = do
  tx <- lookupValueTypeEnv' x
  emitOp $
    unwords
      [ showData (DataLocal x)
      , "="
      , showType tx
      , "call"
      , showData f ++ "(" ++ showArgs args ++ ")"
      ]
  emitAsm cont
emitAsm (_ :< AsmCallTail (f, t) args) = do
  tmp <- newNameWith "tmp"
  let tmpType = getCodType t
  emitOp $
    unwords
      [ showData (DataLocal tmp)
      , "="
      , showType tmpType
      , "tail call"
      , showData f ++ "(" ++ showArgs args ++ ")"
      ]
  emitOp $ unwords ["ret", showType tmpType, showData (DataLocal tmp)]
emitAsm (_ :< AsmBitcast x (d, fromType) toType cont) = do
  emitOp $
    unwords
      [ showData (DataLocal x)
      , "="
      , "bitcast"
      , showType fromType
      , showData d
      , "to"
      , showType toType
      ]
  emitAsm cont
emitAsm (_ :< AsmZeroExtend x (d, fromType) toType cont) = do
  emitOp $
    unwords
      [ showData (DataLocal x)
      , "="
      , "zext"
      , showType fromType
      , showData d
      , "to"
      , showType toType
      ]
  emitAsm cont
emitAsm (_ :< AsmTrunc x (d, fromType) toType cont) = do
  emitOp $
    unwords
      [ showData (DataLocal x)
      , "="
      , "trunc"
      , showType fromType
      , showData d
      , "to"
      , showType toType
      ]
  emitAsm cont
emitAsm (_ :< AsmIntToPointer x (d, fromType) toType cont) = do
  emitOp $
    unwords
      [ showData (DataLocal x)
      , "="
      , "inttoptr"
      , showType fromType
      , showData d
      , "to"
      , showType toType
      ]
  emitAsm cont
emitAsm (_ :< AsmPointerToInt x (d, fromType) toType cont) = do
  emitOp $
    unwords
      [ showData (DataLocal x)
      , "="
      , "ptrtoint"
      , showType fromType
      , showData d
      , "to"
      , showType toType
      ]
  emitAsm cont
emitAsm (_ :< AsmSwitch (d, _) defaultBranch branchList) = do
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
emitAsm (_ :< AsmFree (d, t) cont) = do
  tmp <- newNameWith "tmp"
  emitOp $
    unwords
      [ showData (DataLocal tmp)
      , "="
      , "bitcast"
      , showType t
      , showData d
      , "to"
      , "i8*"
      ]
  emitOp $
    unwords ["call", "void", "@free(i8* " ++ showData (DataLocal tmp) ++ ")"]
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
showData (DataStruct dts) = do
  let ds = map fst dts
  "{" ++ showList showData ds ++ "}*"

showIndex :: [Int] -> String
showIndex [] = ""
showIndex [i] = "i32 " ++ show i
showIndex (i:is) = "i32 " ++ show i ++ ", " ++ showIndex is

showArg :: DataPlus -> String
showArg (d, t) = showType t ++ " " ++ showData d

showArgs :: [DataPlus] -> String
showArgs ds = "(" ++ showList showArg ds ++ ")"

showType :: Value -> String
showType (Value (_ :< ValueVar _)) = "any*"
showType (Value (_ :< ValueConst _)) = undefined
showType (Value (_ :< ValuePi _ _)) = "i8*"
showType (Value (_ :< ValueSigma xts t)) = do
  let ts = map Value $ map snd xts ++ [t]
  "{" ++ showList showType ts ++ "}*"
showType (Value (_ :< ValueIndex i))
  | i `elem` intTypeList = i
showType (Value (_ :< ValueIndex "f32")) = "float"
showType (Value (_ :< ValueIndex "f64")) = "double"
showType (Value (_ :< ValueUp t)) = showType $ Value t
showType (Value (_ :< ValueUniv)) = "i8"
showType v = error $ "Emit.showType: " ++ show v ++ " is not a type"

getCodType :: Value -> Value
getCodType (Value (_ :< ValuePi _ t)) = getCodType $ Value t
getCodType t = t

showTypeNoPtr :: Value -> String
showTypeNoPtr (Value (_ :< ValuePi _ _)) = "i8"
showTypeNoPtr (Value (_ :< ValueSigma xts t)) = do
  let ts = map Value $ map snd xts ++ [t]
  "{" ++ showList showType ts ++ "}"
showTypeNoPtr v = error $ "Emit.showTypeNoPtr:\n" ++ Pr.ppShow v

showList :: (a -> String) -> [a] -> String
showList _ [] = ""
showList f [a] = f a
showList f (a:as) = f a ++ ", " ++ showList f as
