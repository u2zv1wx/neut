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
  forM_ (asmEnv env) $ \(name, asm) -> do
    emitLabel name
    stackSize <- undefined
    extendStack stackSize
    emitAsm asm
    shrinkStack stackSize

emitAsm :: Asm -> WithEnv ()
emitAsm (_ :< AsmReturn _) = emitOp $ unwords ["ret"]
emitAsm (_ :< AsmMov x y cont) = do
  emitOp $ unwords ["movq", showAsmArg y ++ ",", x]
  emitAsm cont
emitAsm (_ :< AsmStoreWithOffset x y i cont) = do
  emitOp $ unwords ["movq", showAsmArg y ++ ",", showRegWithOffset i x]
  emitAsm cont
emitAsm (_ :< AsmLoadWithOffset x y i cont) = do
  emitOp $ unwords ["movq", showRegWithOffset i y ++ ",", x]
  emitAsm cont
emitAsm (_ :< AsmCall _ _ _ cont) = do
  emitOp "call"
  emitAsm cont

extendStack :: Int -> WithEnv ()
extendStack = undefined

shrinkStack :: Int -> WithEnv ()
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
