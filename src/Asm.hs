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
asmCode (CodeReturn d) = do
  result <- newNameWith "ans"
  asmData result d $ AsmReturn $ AsmDataLocal result
asmCode (CodeLet x d cont) = do
  cont' <- asmCode cont
  asmData x d cont'
asmCode (CodeCall x fun args cont) = do
  cont' <- asmCode cont
  f <- newNameWith "fun"
  xs <- mapM (const (newNameWith "arg")) args
  asmData' ((f, fun) : zip xs args) $
    AsmCall x (AsmDataLocal f) (map AsmDataLocal xs) cont'
asmCode (CodeCallTail fun args) = do
  f <- newNameWith "fun"
  xs <- mapM (const (newNameWith "arg")) args
  asmData' ((f, fun) : zip xs args) $
    AsmCallTail (AsmDataLocal f) (map AsmDataLocal xs)
asmCode (CodeSwitch x branchList) = asmSwitch x branchList
asmCode (CodeExtractValue x baseData (i, n) cont) = do
  cont' <- asmCode cont
  tmp <- newNameWith "sigma"
  asmData tmp baseData $ AsmGetElementPtr x (AsmDataLocal tmp) (i, n) cont'
asmCode (CodeFree d cont) = do
  cont' <- asmCode cont
  tmp <- newNameWith "free"
  asmData' [(tmp, d)] $ AsmFree (AsmDataLocal tmp) cont'

asmData :: Identifier -> Data -> Asm -> WithEnv Asm
asmData x (DataLocal y) cont =
  return $ AsmBitcast x (AsmDataLocal y) voidPtr voidPtr cont
asmData x (DataGlobal y) cont =
  return $ AsmBitcast x (AsmDataGlobal y) voidPtr voidPtr cont
asmData x (DataInt32 i) cont =
  return $ AsmBitcast x (AsmDataInt32 i) (LowTypeInt 32) (LowTypeInt 32) cont
asmData reg (DataStruct ds) cont = do
  xs <- mapM (const $ newNameWith "cursor") ds
  let structType = map (const voidPtr) ds
  cont' <- setContent reg (length xs) (zip [0 ..] xs) cont
  asmStruct (zip xs ds) $ AsmAlloc reg structType cont'

asmData' :: [(Identifier, Data)] -> Asm -> WithEnv Asm
asmData' [] cont = return cont
asmData' ((x, d):rest) cont = do
  cont' <- asmData' rest cont
  asmData x d cont'

constructSwitch :: Data -> [(Index, Code)] -> WithEnv (Asm, [(Int, Asm)])
constructSwitch _ [] = lift $ throwE "empty branch"
constructSwitch name ((IndexLabel x, code):_) = do
  code' <- asmCode $ CodeLet x name code
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
  tmp <- newNameWith "switch"
  asmData' [(tmp, name)] $ AsmSwitch (AsmDataLocal tmp) defaultCase caseList

setContent :: Identifier -> Int -> [(Int, Identifier)] -> Asm -> WithEnv Asm
setContent _ _ [] cont = return cont
setContent basePointer length ((index, dataAtIndex):sizeDataList) cont = do
  cont' <- setContent basePointer length sizeDataList cont
  dataPtr <- newNameWith "data"
  cursorPtr <- newNameWith "cursor"
  let tmp = LowTypeInt 100
  return $
    AsmLoad dataPtr (AsmDataLocal dataAtIndex) $
    AsmGetElementPtr cursorPtr (AsmDataLocal basePointer) (index, length) $
    AsmStore (AsmDataLocal dataPtr, tmp) (AsmDataLocal cursorPtr, tmp) cont'

asmStruct :: [(Identifier, Data)] -> Asm -> WithEnv Asm
asmStruct [] cont = return cont
asmStruct ((x, d):xds) cont = do
  cont' <- asmStruct xds cont
  asmData x d cont'

voidPtr :: LowType
voidPtr = LowTypePointer (LowTypeInt 8)
