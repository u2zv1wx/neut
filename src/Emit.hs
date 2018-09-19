module Emit
  ( emit
  ) where

import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.IORef

import           Data

import           Control.Comonad.Cofree

import qualified Text.Show.Pretty           as Pr

import           Data.List

import           Debug.Trace

emit :: WithEnv ()
emit = do
  env <- get
  forM_ (asmEnv env) $ \(name, (args, asm)) -> emitDefine name args asm

emitDefine :: Identifier -> [Identifier] -> Asm -> WithEnv ()
emitDefine name args asm = do
  lamCodLowType <- getCodLowType name
  argStr <- showLamArgs args
  liftIO $
    putStrLn $
    "define " ++
    showLowType lamCodLowType ++ " @" ++ name ++ "(" ++ argStr ++ ") {"
  emitAsm asm
  liftIO $ putStrLn "}"

emitAsm :: Asm -> WithEnv ()
emitAsm (AsmReturn x) = do
  t <- lookupTypeEnv' x >>= toLowType
  emitOp $ unwords ["ret", showLowType t, x]
emitAsm (AsmLet x (AsmArgReg y) cont) = do
  tmp <- newNameWith "tmp"
  ty <- lookupTypeEnv' y >>= toLowType
  let typ = LowTypePointer ty
  emitOp $ unwords [tmp, "= alloca", showLowType ty]
  emitOp $ unwords ["store", showLowType ty, y ++ ",", showLowType typ, tmp]
  emitOp $ unwords [x, "= load", showLowType ty ++ ",", showLowType typ, tmp]
  emitAsm cont
emitAsm (AsmLet x (AsmArgImmediate i) cont) = do
  tmp <- newNameWith "tmp"
  let ty = LowTypeInt 32
  let typ = LowTypePointer ty
  emitOp $ unwords [tmp, "= alloca", showLowType ty]
  emitOp $
    unwords ["store", showLowType ty, show i ++ ",", showLowType typ, tmp]
  emitOp $ unwords [x, "= load", showLowType ty ++ ",", showLowType typ, tmp]
  emitAsm cont
emitAsm (AsmExtractValue x (base, t) i cont) = do
  tmp <- newName
  let tp = LowTypePointer t
  emitOp $
    unwords
      [ tmp ++ " = getelementptr"
      , showLowType t ++ ","
      , showLowType tp
      , base
      , ", "
      , showIndexList [0, i]
      ]
  tx <- lookupTypeEnv' x >>= toLowType
  let txp = LowTypePointer tx
  emitOp $ unwords [x ++ " = load", showLowType tx ++ ",", showLowType txp, tmp]
  emitAsm cont
emitAsm (AsmInsertValue val (base, t) i cont) = do
  tmp <- newName
  let tp = LowTypePointer t
  emitOp $
    unwords
      [ tmp ++ " = getelementptr"
      , showLowType t ++ ","
      , showLowType tp
      , base
      , ", "
      , showIndexList [0, i]
      ]
  valType <- asmArgType val
  -- let valType' = LowTypePointer valType
  valStr <- showAsmArg val
  emitOp $ unwords ["store", valStr ++ ",", showLowType valType, tmp]
  emitAsm cont
emitAsm (AsmCall x label args cont) = do
  codLowTypeStr <- showLowType <$> getCodLowType label
  label' <- toRegName label
  argStr <- showAsmArgs args
  emitOp $ unwords [x, "= call", codLowTypeStr, label', "(" ++ argStr ++ ")"]
  emitAsm cont
emitAsm (AsmMalloc x t cont) = do
  let size = sizeOfLowType t
  emitOp $ unwords [x, "= call i8* @malloc(i32 " ++ show size ++ ")"]
  emitAsm cont

getCodLowType :: Identifier -> WithEnv LowType
getCodLowType name = do
  lamType <- lookupTypeEnv' name
  (lamCodType, _) <- toPiSeq lamType
  toLowType lamCodType

showAsmArg :: AsmArg -> WithEnv String
showAsmArg (AsmArgReg x) = do
  t <- lookupTypeEnv' x >>= toLowType
  return $ unwords [showLowType t, "%" ++ x]
showAsmArg (AsmArgImmediate i) = return $ "$" ++ show i

showLamArgs :: [Identifier] -> WithEnv String
showLamArgs [] = return ""
showLamArgs [x] = do
  t <- lookupTypeEnv' x >>= toLowType
  return $ showLowType t
showLamArgs (x:y:rest) = do
  s <- showLamArgs $ y : rest
  t <- lookupTypeEnv' x >>= toLowType
  return $ showLowType t ++ ", " ++ s

showAsmArgs :: [AsmArg] -> WithEnv String
showAsmArgs [] = return ""
showAsmArgs [x] = showAsmArg x
showAsmArgs (x:y:rest) = do
  s1 <- showAsmArg x
  s2 <- showAsmArgs $ y : rest
  return $ s1 ++ ", " ++ s2

emitOp :: String -> WithEnv ()
emitOp s = liftIO $ putStrLn $ "  " ++ s

emitGlobalLabel :: Identifier -> WithEnv ()
emitGlobalLabel label = liftIO $ putStrLn $ "  " ++ ".globl " ++ label

showLowType :: LowType -> String
showLowType (LowTypeInt i)     = "i" ++ show i
showLowType (LowTypePointer t) = showLowType t ++ "*"
showLowType (LowTypeStruct ts) = "{" ++ showLowTypeList ts ++ "}"

showLowTypeList :: [LowType] -> String
showLowTypeList [] = ""
showLowTypeList [t] = showLowType t
showLowTypeList (t1:t2:ts) = do
  let s1 = showLowType t1
  let s2 = showLowTypeList $ t2 : ts
  s1 ++ ", " ++ s2

showIndexList :: [Int] -> String
showIndexList [] = ""
showIndexList [i] = "i32 " ++ show i
showIndexList (i:j:is) = do
  let s1 = "i32" ++ show i
  let s2 = showIndexList $ j : is
  s1 ++ ", " ++ s2

asmArgType :: AsmArg -> WithEnv LowType
asmArgType (AsmArgReg x)       = lookupTypeEnv' x >>= toLowType
asmArgType (AsmArgImmediate _) = return $ LowTypeInt 32
