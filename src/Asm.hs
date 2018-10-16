module Asm
  ( assemblize
  ) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans.Except
import Data.IORef

import Data
import Reduce
import Util

import Control.Comonad.Cofree

import qualified Text.Show.Pretty as Pr

import Debug.Trace

assemblize :: WithEnv ()
assemblize = do
  env <- get
  forM_ (codeEnv env) $ \(name, (args, codeRef)) -> do
    code <- liftIO $ readIORef codeRef
    asm <- asmCode code
    insAsmEnv name args asm

asmCode :: Code -> WithEnv Asm
asmCode (CodeReturn d) = return $ AsmReturn d
asmCode (CodeCall x fun args cont) = do
  cont' <- asmCode cont
  return $ AsmCall x fun args cont'
asmCode (CodeCallTail fun args) = return $ AsmCallTail fun args
asmCode (CodeSwitch x branchList) = asmSwitch x branchList
asmCode (CodeExtractValue x basePointer (i, n) cont) = do
  cont' <- asmCode cont
  return $ AsmGetElementPtr x basePointer (i, n) cont'
asmCode (CodeFree x cont) = do
  cont' <- asmCode cont
  return $ AsmFree x cont'

constructSwitch :: Data -> [(Index, Code)] -> WithEnv (Asm, [(Int, Asm)])
constructSwitch _ [] = lift $ throwE "empty branch"
constructSwitch _ [(_, code)] = do
  code' <- asmCode code
  return (code', [])
constructSwitch name ((IndexLabel x, code):_) = do
  code' <- asmCode $ substCode [(x, name)] code
  return (code', [])
constructSwitch _ ((IndexDefault, code):_) = do
  code' <- asmCode code
  return (code', [])
constructSwitch name ((IndexInteger i, code):rest) = do
  code' <- asmCode code
  (defaultCase, caseList) <- constructSwitch name rest
  return (defaultCase, (i, code') : caseList)

asmSwitch :: Data -> [(Index, Code)] -> WithEnv Asm
asmSwitch name branchList = do
  (defaultCase, caseList) <- constructSwitch name branchList
  return $ AsmSwitch name defaultCase caseList
