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
  let funPtrType = toFunPtrType args
  cast <- newNameWith "cast"
  asmData' ((f, fun) : zip xs args) $
    AsmBitcast cast (AsmDataLocal f) voidPtr funPtrType $
    AsmCall x (AsmDataLocal cast) (map AsmDataLocal xs) cont'
asmCode (CodeCallTail fun args) = do
  f <- newNameWith "fun"
  xs <- mapM (const (newNameWith "arg")) args
  let funPtrType = toFunPtrType args
  cast <- newNameWith "cast"
  asmData' ((f, fun) : zip xs args) $
    AsmBitcast cast (AsmDataLocal f) voidPtr funPtrType $
    AsmCallTail (AsmDataLocal cast) (map AsmDataLocal xs)
asmCode (CodeSwitch x branchList) = asmSwitch x branchList
asmCode (CodeExtractValue x baseData (i, n) cont) = do
  cont' <- asmCode cont
  tmp <- newNameWith "sigma"
  cast <- newNameWith "cast"
  let structPtrType = toStructPtrType [1 .. n]
  loader <- newNameWith "loader"
  asmData tmp baseData $
    AsmBitcast cast (AsmDataLocal tmp) voidPtr structPtrType $
    AsmGetElementPtr loader (AsmDataLocal cast) (i, n) $
    AsmLoad x (AsmDataLocal loader) cont'
asmCode (CodeFree d cont) = do
  cont' <- asmCode cont
  tmp <- newNameWith "free"
  asmData' [(tmp, d)] $ AsmFree (AsmDataLocal tmp) cont'

asmData :: Identifier -> Data -> Asm -> WithEnv Asm
asmData x (DataLocal y) cont =
  return $ AsmBitcast x (AsmDataLocal y) voidPtr voidPtr cont
asmData x (DataGlobal y) cont = do
  cenv <- gets codeEnv
  case lookup y cenv of
    Nothing -> do
      liftIO $ putStrLn $ "no such global label defined: " ++ y -- FIXME
      return $ AsmBitcast x (AsmDataGlobal y) voidPtr voidPtr cont
    Just (args, _) -> do
      let funPtrType = toFunPtrType args
      return $ AsmBitcast x (AsmDataGlobal y) funPtrType voidPtr cont
asmData x (DataInt32 i) cont =
  return $ AsmIntToPointer x (AsmDataInt32 i) (LowTypeInt 32) voidPtr cont
asmData reg (DataStruct ds) cont = do
  xs <- mapM (const $ newNameWith "cursor") ds
  cast <- newNameWith "cast"
  let ts = map (const voidPtr) ds
  let structPtrType = LowTypePointer $ LowTypeStruct ts
  cont'' <- setContent cast (length xs) (zip [0 ..] xs) cont
  asmStruct (zip xs ds) $
    AsmAlloc reg ts $ -- the result of malloc is i8*
    AsmBitcast cast (AsmDataLocal reg) voidPtr structPtrType cont''
asmData reg (DataArith kind@(_, int) d1 d2) cont = do
  x1 <- newNameWith "arg"
  x2 <- newNameWith "arg"
  cast1 <- newNameWith "cast"
  cast2 <- newNameWith "cast"
  tmp <- newNameWith "cast"
  asmStruct [(x1, d1), (x2, d2)] $
    AsmPointerToInt cast1 (AsmDataLocal x1) voidPtr int $
    AsmPointerToInt cast2 (AsmDataLocal x2) voidPtr int $
    AsmArith tmp kind (AsmDataLocal cast1) (AsmDataLocal cast2) $
    AsmIntToPointer reg (AsmDataLocal tmp) int voidPtr cont

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
  cast <- newNameWith "cast"
  asmData' [(tmp, name)] $
    AsmPointerToInt cast (AsmDataLocal tmp) voidPtr (LowTypeInt 64) $
    AsmSwitch (AsmDataLocal cast) defaultCase caseList

setContent :: Identifier -> Int -> [(Int, Identifier)] -> Asm -> WithEnv Asm
setContent _ _ [] cont = return cont
setContent basePointer length ((index, dataAtIndex):sizeDataList) cont = do
  cont' <- setContent basePointer length sizeDataList cont
  addr <- newNameWith "addr"
  cursorPtr <- newNameWith "cursor"
  castPtr <- newNameWith "cast"
  loader <- newNameWith "loader"
  return $
    AsmGetElementPtr loader (AsmDataLocal basePointer) (index, length) $
    AsmLoad cursorPtr (AsmDataLocal loader) $
    AsmBitcast castPtr (AsmDataLocal cursorPtr) voidPtr int64ptr $
    AsmPointerToInt addr (AsmDataLocal dataAtIndex) voidPtr int64 $
    AsmStore (AsmDataLocal addr, int64) (AsmDataLocal castPtr, int64ptr) cont'

asmStruct :: [(Identifier, Data)] -> Asm -> WithEnv Asm
asmStruct [] cont = return cont
asmStruct ((x, d):xds) cont = do
  cont' <- asmStruct xds cont
  asmData x d cont'

voidPtr :: LowType
voidPtr = LowTypePointer $ LowTypeInt 8

int64 :: LowType
int64 = LowTypeInt 64

int64ptr :: LowType
int64ptr = LowTypePointer $ LowTypeInt 64

toFunPtrType :: [a] -> LowType
toFunPtrType xs = do
  let funType = LowTypeFunction (map (const voidPtr) xs) voidPtr
  LowTypePointer funType

toStructPtrType :: [a] -> LowType
toStructPtrType xs = do
  let structType = LowTypeStruct $ map (const voidPtr) xs
  LowTypePointer structType
