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
asmCode (CodePrint t d cont) = do
  cont' <- asmCode cont
  tmp <- newNameWith "item"
  cast <- newNameWith "cast"
  asmData' [(tmp, d)] $
    AsmPointerToInt cast (AsmDataLocal tmp) voidPtr t $
    AsmPrint t (AsmDataLocal cast) cont'

asmData :: Identifier -> Data -> Asm -> WithEnv Asm
asmData x (DataLocal y) cont =
  return $ AsmBitcast x (AsmDataLocal y) voidPtr voidPtr cont
asmData x (DataGlobal y) cont = do
  cenv <- gets codeEnv
  case lookup y cenv of
    Nothing -> do
      liftIO $ putStrLn $ "no such global label defined: " ++ y -- FIXME
      -- todo: decleare y
      return $ AsmBitcast x (AsmDataGlobal y) voidPtr voidPtr cont
    Just (args, _) -> do
      let funPtrType = toFunPtrType args
      return $ AsmBitcast x (AsmDataGlobal y) funPtrType voidPtr cont
asmData x (DataInt i) cont =
  return $ AsmIntToPointer x (AsmDataInt i) (LowTypeSignedInt 64) voidPtr cont
asmData x (DataFloat16 f) cont = do
  cast <- newNameWith "cast"
  return $
    AsmBitcast cast (AsmDataFloat f) (LowTypeFloat 16) (LowTypeSignedInt 16) $
    AsmIntToPointer x (AsmDataLocal cast) (LowTypeSignedInt 16) voidPtr cont
asmData x (DataFloat32 f) cont = do
  cast <- newNameWith "cast"
  return $
    AsmBitcast cast (AsmDataFloat f) (LowTypeFloat 32) (LowTypeSignedInt 32) $
    AsmIntToPointer x (AsmDataLocal cast) (LowTypeSignedInt 32) voidPtr cont
asmData x (DataFloat64 f) cont = do
  cast <- newNameWith "cast"
  return $
    AsmBitcast cast (AsmDataFloat f) (LowTypeFloat 64) (LowTypeSignedInt 64) $
    AsmIntToPointer x (AsmDataLocal cast) (LowTypeSignedInt 64) voidPtr cont
asmData reg (DataStruct []) cont = asmData reg (DataInt 0) cont
asmData reg (DataStruct [d]) cont = asmData reg d cont
asmData reg (DataStruct ds) cont = do
  xs <- mapM (const $ newNameWith "cursor") ds
  cast <- newNameWith "cast"
  let ts = map (const voidPtr) ds
  let structPtrType = LowTypePointer $ LowTypeStruct ts
  cont'' <- setContent cast (length xs) (zip [0 ..] xs) cont
  asmStruct (zip xs ds) $
    AsmAlloc reg ts $ -- the result of malloc is i8*
    AsmBitcast cast (AsmDataLocal reg) voidPtr structPtrType cont''
asmData reg (DataArith kind@(_, intType) d1 d2) cont
  | intType `elem` intLowTypeList = do
    x1 <- newNameWith "arg"
    x2 <- newNameWith "arg"
    cast1 <- newNameWith "cast"
    cast2 <- newNameWith "cast"
    tmp <- newNameWith "arith"
    asmStruct [(x1, d1), (x2, d2)] $
      AsmPointerToInt cast1 (AsmDataLocal x1) voidPtr intType $
      AsmPointerToInt cast2 (AsmDataLocal x2) voidPtr intType $
      AsmArith tmp kind (AsmDataLocal cast1) (AsmDataLocal cast2) $
      AsmIntToPointer reg (AsmDataLocal tmp) intType voidPtr cont
asmData reg (DataArith kind@(_, LowTypeFloat i) d1 d2) cont = do
  x1 <- newNameWith "arg"
  x2 <- newNameWith "arg"
  cast11 <- newNameWith "cast"
  cast12 <- newNameWith "float"
  cast21 <- newNameWith "cast"
  cast22 <- newNameWith "float"
  tmp <- newNameWith "arith"
  uncast <- newNameWith "uncast"
  let intType = LowTypeSignedInt i
  asmStruct [(x1, d1), (x2, d2)] $
    -- cast the first argument from i8* to float
    AsmPointerToInt cast11 (AsmDataLocal x1) voidPtr intType $
    AsmBitcast cast12 (AsmDataLocal cast11) intType (LowTypeFloat i) $
    -- cast the second argument from i8* to float
    AsmPointerToInt cast21 (AsmDataLocal x2) voidPtr intType $
    AsmBitcast cast22 (AsmDataLocal cast21) intType (LowTypeFloat i) $
    -- compute
    AsmArith tmp kind (AsmDataLocal cast12) (AsmDataLocal cast22) $
    -- cast the result from float to i8*
    AsmBitcast uncast (AsmDataLocal tmp) (LowTypeFloat i) intType $
    AsmIntToPointer reg (AsmDataLocal uncast) intType voidPtr cont
asmData _ DataArith {} _ = lift $ throwE "Asm.asmData: type error"

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
constructSwitch _ ((IndexFloat _, _):_) = undefined -- IEEE754 float equality!

asmSwitch :: Data -> [(Index, Code)] -> WithEnv Asm
asmSwitch name branchList = do
  (defaultCase, caseList) <- constructSwitch name branchList
  tmp <- newNameWith "switch"
  cast <- newNameWith "cast"
  asmData' [(tmp, name)] $
    AsmPointerToInt cast (AsmDataLocal tmp) voidPtr (LowTypeSignedInt 64) $
    AsmSwitch (AsmDataLocal cast) defaultCase caseList

setContent :: Identifier -> Int -> [(Int, Identifier)] -> Asm -> WithEnv Asm
setContent _ _ [] cont = return cont
setContent basePointer length ((index, dataAtIndex):sizeDataList) cont = do
  cont' <- setContent basePointer length sizeDataList cont
  loader <- newNameWith "loader"
  let voidPtrPtr = LowTypePointer voidPtr
  return $
    AsmGetElementPtr loader (AsmDataLocal basePointer) (index, length) $
    AsmStore
      (AsmDataLocal dataAtIndex, voidPtr)
      (AsmDataLocal loader, voidPtrPtr)
      cont'

asmStruct :: [(Identifier, Data)] -> Asm -> WithEnv Asm
asmStruct [] cont = return cont
asmStruct ((x, d):xds) cont = do
  cont' <- asmStruct xds cont
  asmData x d cont'

voidPtr :: LowType
voidPtr = LowTypePointer $ LowTypeSignedInt 8

toFunPtrType :: [a] -> LowType
toFunPtrType xs = do
  let funType = LowTypeFunction (map (const voidPtr) xs) voidPtr
  LowTypePointer funType

toStructPtrType :: [a] -> LowType
toStructPtrType xs = do
  let structType = LowTypeStruct $ map (const voidPtr) xs
  LowTypePointer structType
