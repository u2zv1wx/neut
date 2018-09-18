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
emitAsm (_ :< AsmMov x y cont) = do
  emitOp $ unwords ["movq", showAsmArg y ++ ",", x]
  emitAsm cont
emitAsm (_ :< AsmLoadWithOffset offset base dest cont) = do
  emitOp $ unwords ["movq", showRegWithOffset offset base ++ ",", dest]
  emitAsm cont
emitAsm (_ :< AsmStoreWithOffset val offset base cont) = do
  emitOp $
    unwords ["movq", showAsmArg val ++ ",", showRegWithOffset offset base]
  emitAsm cont
emitAsm (_ :< AsmCall _ _ _ cont) = do
  emitOp "call"
  emitAsm cont
emitAsm (meta :< AsmPush x cont) = do
  rsp <- undefined
  offset <- computeOffset x
  emitAsm $ meta :< AsmStoreWithOffset (AsmArgReg x) offset rsp cont
emitAsm (meta :< AsmPop x cont) = do
  rsp <- undefined
  offset <- computeOffset x
  emitAsm $ meta :< AsmLoadWithOffset offset rsp x cont
emitAsm (_ :< AsmAddInt64 arg dest cont) = do
  emitOp $ unwords ["addq", showAsmArg arg, dest]
  emitAsm cont
emitAsm (_ :< AsmSubInt64 arg dest cont) = do
  emitOp $ unwords ["subq", showAsmArg arg, dest]
  emitAsm cont

showAsmArg :: AsmArg -> String
showAsmArg (AsmArgReg x)       = "%" ++ x
showAsmArg (AsmArgImmediate i) = "$" ++ show i

showRegWithOffset :: Int -> Identifier -> Identifier
showRegWithOffset offset x =
  show offset ++ "(" ++ showAsmArg (AsmArgReg x) ++ ")"

emitOp :: String -> WithEnv ()
emitOp s = liftIO $ putStrLn $ "  " ++ s

emitLabel :: String -> WithEnv ()
emitLabel s = liftIO $ putStrLn $ s ++ ":"

emitGlobalLabel :: Identifier -> WithEnv ()
emitGlobalLabel label = liftIO $ putStrLn $ "  " ++ ".globl " ++ label

-- save/restore all the live variables before function call
insSaveRestore :: Asm -> WithEnv Asm
insSaveRestore (meta :< AsmReturn x) = return $ meta :< AsmReturn x
insSaveRestore (meta :< AsmMov x y cont) = do
  cont' <- insSaveRestore cont
  return $ meta :< AsmMov x y cont'
insSaveRestore (meta :< AsmStoreWithOffset val offset base cont) = do
  cont' <- insSaveRestore cont
  return $ meta :< AsmStoreWithOffset val offset base cont'
insSaveRestore (meta :< AsmLoadWithOffset offset base dest cont) = do
  cont' <- insSaveRestore cont
  return $ meta :< AsmLoadWithOffset offset base dest cont'
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
computeSizeList (_ :< AsmMov _ _ cont) = computeSizeList cont
computeSizeList (_ :< AsmStoreWithOffset _ _ _ cont) = computeSizeList cont
computeSizeList (_ :< AsmLoadWithOffset _ _ _ cont) = computeSizeList cont
computeSizeList (_ :< AsmCall _ _ _ cont) = computeSizeList cont
computeSizeList (_ :< AsmPush x cont) = do
  size <- sizeOf x
  insSizeEnv x size
  computeSizeList cont
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
insShrink (meta :< AsmMov x y cont) = do
  cont' <- insShrink cont
  return $ meta :< AsmMov x y cont'
insShrink (meta :< AsmStoreWithOffset val offset base cont) = do
  cont' <- insShrink cont
  return $ meta :< AsmStoreWithOffset val offset base cont'
insShrink (meta :< AsmLoadWithOffset offset base dest cont) = do
  cont' <- insShrink cont
  return $ meta :< AsmLoadWithOffset offset base dest cont'
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
  rsp <- undefined
  addMeta $ AsmSubInt64 (AsmArgImmediate size) rsp asm

shrinkStack :: Asm -> WithEnv Asm
shrinkStack asm = do
  env <- get
  let size = alignedSize $ sum $ map snd $ sizeEnv env
  rsp <- undefined
  addMeta $ AsmAddInt64 (AsmArgImmediate size) rsp asm

-- find the least y such that y >= x && y mod 16 == 8
alignedSize :: Int -> Int
alignedSize x = undefined
