module Emit
  ( emit
  , emitGlobalLabel
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
  forM_ (asmEnv env) $ \(name, asm) -> do
    emitLabel name
    modify (\e -> e {sizeEnv = []})
    computeSizeList asm
    asm' <- insExtendShrink asm
    asm'' <- insSaveRestore asm'
    emitAsm asm''

emitAsm :: Asm -> WithEnv ()
emitAsm (_ :< AsmReturn _) = emitOp $ unwords ["ret"]
emitAsm (_ :< AsmLet x (AsmArgReg y) cont) = do
  x' <- showReg x
  y' <- showReg y
  emitOp $ unwords ["movq", y' ++ ",", x']
  emitAsm cont
emitAsm (_ :< AsmLet x (AsmArgLabel label) cont) = do
  x' <- showReg x
  emitOp $ unwords ["leaq", label ++ "(%rip),", x']
  emitAsm cont
emitAsm (_ :< AsmLet x (AsmArgImmediate i) cont) = do
  x' <- showReg x
  emitOp $ unwords ["movq", show i, x']
  emitAsm cont
emitAsm (_ :< AsmExtractValue dest base offset cont) = do
  base' <- showReg base
  dest' <- showReg dest
  emitOp $ unwords ["movq", showRegWithOffset offset base' ++ ",", dest']
  emitAsm cont
emitAsm (_ :< AsmInsertValue val base offset cont) = do
  val' <- showAsmArg val
  base' <- showReg base
  emitOp $ unwords ["movq", val' ++ ",", showRegWithOffset offset base']
  emitAsm cont
emitAsm (_ :< AsmCall _ (AsmArgReg x) _ cont) = do
  x' <- toRegName x
  emitOp $ unwords ["call", "*" ++ x']
  emitAsm cont
emitAsm (_ :< AsmCall _ (AsmArgLabel label) _ cont) = do
  emitOp $ unwords ["call", label]
  emitAsm cont
emitAsm (_ :< AsmCall _ (AsmArgImmediate _) _ _) =
  liftIO $ putStrLn "emitAsm.AsmCall: immediate?"
emitAsm (meta :< AsmPush x cont) = do
  rsp <- getRSP
  offset <- computeOffset x
  emitAsm $ meta :< AsmInsertValue (AsmArgReg x) rsp offset cont
emitAsm (meta :< AsmPop dest cont) = do
  rsp <- getRSP
  offset <- computeOffset dest
  emitAsm $ meta :< AsmExtractValue dest rsp offset cont
emitAsm (_ :< AsmAddInt64 arg dest cont) = do
  arg' <- showAsmArg arg
  dest' <- showReg dest
  emitOp $ unwords ["addq", arg' ++ ",", dest']
  emitAsm cont
emitAsm (_ :< AsmSubInt64 arg dest cont) = do
  arg' <- showAsmArg arg
  dest' <- showReg dest
  emitOp $ unwords ["subq", arg' ++ ",", dest']
  emitAsm cont

showAsmArg :: AsmArg -> WithEnv String
showAsmArg (AsmArgReg x)       = showReg x
showAsmArg (AsmArgLabel x)     = return x
showAsmArg (AsmArgImmediate i) = return $ "$" ++ show i

showReg :: Identifier -> WithEnv String
showReg x = do
  x' <- toRegName x
  return $ "%" ++ x'

emitOp :: String -> WithEnv ()
emitOp s = liftIO $ putStrLn $ "  " ++ s

emitGlobalLabel :: Identifier -> WithEnv ()
emitGlobalLabel label = liftIO $ putStrLn $ "  " ++ ".globl " ++ label

showRegWithOffset :: Int -> Identifier -> Identifier
showRegWithOffset offset x = show offset ++ "(" ++ x ++ ")"

emitLabel :: String -> WithEnv ()
emitLabel s = liftIO $ putStrLn $ s ++ ":"

insSaveRestore :: Asm -> WithEnv Asm
insSaveRestore (meta :< AsmReturn x) = return $ meta :< AsmReturn x
insSaveRestore (meta :< AsmLet x y cont) = do
  cont' <- insSaveRestore cont
  return $ meta :< AsmLet x y cont'
insSaveRestore (meta :< AsmInsertValue val offset base cont) = do
  cont' <- insSaveRestore cont
  return $ meta :< AsmInsertValue val offset base cont'
insSaveRestore (meta :< AsmExtractValue offset base dest cont) = do
  cont' <- insSaveRestore cont
  return $ meta :< AsmExtractValue offset base dest cont'
insSaveRestore (meta :< AsmCall x fun args cont) = do
  let lvs = asmMetaLive meta
  cont' <- insSaveRestore cont
  cont'' <- insRestore lvs cont'
  insSave lvs $ meta :< AsmCall x fun args cont''
insSaveRestore (meta :< AsmPush x cont) = do
  cont' <- insSaveRestore cont
  return $ meta :< AsmPush x cont'
insSaveRestore (meta :< AsmPop x cont) = do
  cont' <- insSaveRestore cont
  return $ meta :< AsmPop x cont'
insSaveRestore (meta :< AsmAddInt64 arg dest cont) = do
  cont' <- insSaveRestore cont
  return $ meta :< AsmAddInt64 arg dest cont'
insSaveRestore (meta :< AsmSubInt64 arg dest cont) = do
  cont' <- insSaveRestore cont
  return $ meta :< AsmSubInt64 arg dest cont'

insSave :: [Identifier] -> Asm -> WithEnv Asm
insSave [] asm = return asm
insSave (x:xs) asm = do
  tmp <- insSave xs asm
  addMeta $ AsmPush x tmp

insRestore :: [Identifier] -> Asm -> WithEnv Asm
insRestore [] asm = return asm
insRestore (x:xs) asm = do
  tmp <- insRestore xs asm
  addMeta $ AsmPop x tmp

computeSizeList :: Asm -> WithEnv ()
computeSizeList (_ :< AsmReturn _) = return ()
computeSizeList (_ :< AsmLet _ _ cont) = computeSizeList cont
computeSizeList (_ :< AsmInsertValue _ _ _ cont) = computeSizeList cont
computeSizeList (_ :< AsmExtractValue _ _ _ cont) = computeSizeList cont
computeSizeList (_ :< AsmCall _ _ _ cont) = computeSizeList cont
computeSizeList (_ :< AsmPush x cont) = do
  computeSizeList cont
  size <- sizeOf x
  insSizeEnv x size
computeSizeList (_ :< AsmPop _ cont) = computeSizeList cont
computeSizeList (_ :< AsmAddInt64 _ _ cont) = computeSizeList cont
computeSizeList (_ :< AsmSubInt64 _ _ cont) = computeSizeList cont

computeOffset :: Identifier -> WithEnv Int
computeOffset x = do
  env <- get
  let prefixList = takeWhile (\(y, _) -> x /= y) $ sizeEnv env
  return $ sum $ map snd prefixList

-- extend/shrink the stack pointer before/after executing function body
insExtendShrink :: Asm -> WithEnv Asm
insExtendShrink asm = do
  asm' <- extendStack asm
  insShrink asm'

insShrink :: Asm -> WithEnv Asm
insShrink (meta :< AsmReturn x) = shrinkStack $ meta :< AsmReturn x
insShrink (meta :< AsmLet x y cont) = do
  cont' <- insShrink cont
  return $ meta :< AsmLet x y cont'
insShrink (meta :< AsmInsertValue val offset base cont) = do
  cont' <- insShrink cont
  return $ meta :< AsmInsertValue val offset base cont'
insShrink (meta :< AsmExtractValue offset base dest cont) = do
  cont' <- insShrink cont
  return $ meta :< AsmExtractValue offset base dest cont'
insShrink (meta :< AsmCall x fun args cont) = do
  cont' <- insShrink cont
  return $ meta :< AsmCall x fun args cont'
insShrink (meta :< AsmPush x cont) = do
  cont' <- insShrink cont
  return $ meta :< AsmPush x cont'
insShrink (meta :< AsmPop x cont) = do
  cont' <- insShrink cont
  return $ meta :< AsmPop x cont'
insShrink (meta :< AsmAddInt64 arg dest cont) = do
  cont' <- insShrink cont
  return $ meta :< AsmAddInt64 arg dest cont'
insShrink (meta :< AsmSubInt64 arg dest cont) = do
  cont' <- insShrink cont
  return $ meta :< AsmSubInt64 arg dest cont'

extendStack :: Asm -> WithEnv Asm
extendStack asm = do
  env <- get
  let size = alignedSize $ sum $ map snd $ sizeEnv env
  rsp <- getRSP
  addMeta $ AsmSubInt64 (AsmArgImmediate size) rsp asm

shrinkStack :: Asm -> WithEnv Asm
shrinkStack asm = do
  env <- get
  let size = alignedSize $ sum $ map snd $ sizeEnv env
  rsp <- getRSP
  addMeta $ AsmAddInt64 (AsmArgImmediate size) rsp asm

-- find the least y such that y >= x && y mod 16 == 8
alignedSize :: Int -> Int
alignedSize x =
  if x `mod` 16 == 8
    then x
    else alignedSize (x + 1)
