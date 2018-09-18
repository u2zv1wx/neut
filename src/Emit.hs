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
    extendStack
    insSaveRestore asm >>= emitAsm

emitAsm :: Asm -> WithEnv ()
emitAsm (_ :< AsmReturn _) = do
  shrinkStack
  emitOp $ unwords ["ret"]
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
  offset <- undefined x
  rsp <- undefined
  emitAsm $ meta :< AsmStoreWithOffset (AsmArgReg x) offset rsp cont
emitAsm (meta :< AsmPop x cont) = do
  offset <- undefined x
  rsp <- undefined
  emitAsm $ meta :< AsmLoadWithOffset offset rsp x cont

extendStack :: WithEnv ()
extendStack = undefined

shrinkStack :: WithEnv ()
shrinkStack = undefined

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

insSaveRestore :: Asm -> WithEnv Asm
insSaveRestore (meta :< AsmReturn x) = return $ meta :< AsmReturn x
insSaveRestore (meta :< AsmMov x y cont) = do
  cont' <- insSaveRestore cont
  return $ meta :< AsmMov x y cont'
insSaveRestore (meta :< AsmStoreWithOffset x y i cont) = do
  cont' <- insSaveRestore cont
  return $ meta :< AsmStoreWithOffset x y i cont'
insSaveRestore (meta :< AsmLoadWithOffset x y i cont) = do
  cont' <- insSaveRestore cont
  return $ meta :< AsmLoadWithOffset x y i cont'
insSaveRestore (meta :< AsmCall x fun args cont) = do
  let lvs = asmMetaLive meta
  cont' <- insSaveRestore cont
  tmp <- insRestore lvs cont'
  insSave lvs $ meta :< AsmCall x fun args tmp
insSaveRestore (meta :< AsmPush x cont) = do
  cont' <- insSaveRestore cont
  return $ meta :< AsmPush x cont'
insSaveRestore (meta :< AsmPop x cont) = do
  cont' <- insSaveRestore cont
  return $ meta :< AsmPop x cont'

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

computeOffset :: Identifier -> WithEnv Int
computeOffset x = do
  env <- get
  let prefixList = takeWhile (\(y, _) -> x /= y) $ sizeEnv env
  return $ sum $ map snd prefixList
