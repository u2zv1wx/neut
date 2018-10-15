module Asm
  ( asmCodeEnv
  , asmCode
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

asmCodeEnv :: WithEnv ()
asmCodeEnv = do
  env <- get
  forM_ (codeEnv env) $ \(name, (args, codeRef)) -> do
    xs <- mapM (const createIntVar) args
    code <- liftIO $ readIORef codeRef
    asm <- asmCode code
    asm' <- asmCastFromInt64 (zip xs args) asm
    insAsmEnv name xs asm'

createIntVar :: WithEnv Identifier
createIntVar = do
  intMeta <- newNameWith "meta"
  x <- newNameWith "arg"
  insValueTypeEnv x $ Value $ intMeta :< ValueIndex "i64"
  return x

asmCode :: Code -> WithEnv Asm
asmCode (CodeReturn (d, t)) = do
  castedResult <- newNameWith "cast"
  intMeta <- newNameWith "meta"
  insValueTypeEnv castedResult $ Value $ intMeta :< ValueIndex "i64"
  ret <- addMeta $ AsmReturn (DataLocal castedResult, t)
  result <- newNameWith "tmp"
  insValueTypeEnv result t
  asmCastToInt64 [((d, t), castedResult)] ret
asmCode (CodeCall x fun args cont) = do
  cont' <- asmCode cont
  asmCodeCall x fun args cont'
asmCode (CodeCallTail fun args) = do
  xs <- mapM (const createIntVar) args
  let ts = map snd args
  call <- addMeta $ AsmCallTail fun $ zip (map DataLocal xs) ts
  asmCastToInt64 (zip args xs) call
asmCode (CodeSwitch x branchList) = asmSwitch x branchList
asmCode (CodeExtractValue x basePointer i cont) = do
  cont' <- asmCode cont
  addMeta $ AsmGetElementPtr x basePointer i cont'
asmCode (CodeFree x cont) = do
  cont' <- asmCode cont
  addMeta $ AsmFree x cont'

constructSwitch :: DataPlus -> [(Index, Code)] -> WithEnv (Asm, [(Int, Asm)])
constructSwitch _ [] = lift $ throwE "empty branch"
constructSwitch _ [(_, code)] = do
  code' <- asmCode code
  return (code', [])
constructSwitch (name, _) ((IndexLabel x, code):_) = do
  code' <- asmCode $ substCode [(x, name)] code
  return (code', [])
constructSwitch _ ((IndexDefault, code):_) = do
  code' <- asmCode code
  return (code', [])
constructSwitch name ((IndexInteger i, code):rest) = do
  code' <- asmCode code
  (defaultCase, caseList) <- constructSwitch name rest
  return (defaultCase, (i, code') : caseList)

asmSwitch :: DataPlus -> [(Index, Code)] -> WithEnv Asm
asmSwitch name branchList = do
  (defaultCase, caseList) <- constructSwitch name branchList
  addMeta $ AsmSwitch name defaultCase caseList

asmCodeCall :: Identifier -> DataPlus -> [DataPlus] -> Asm -> WithEnv Asm
asmCodeCall x fun args cont = do
  resInt <- createIntVar
  cont' <- asmCastFromInt64 [(resInt, x)] cont
  xs <- mapM (const createIntVar) args
  let xs' = map DataLocal xs
  let ts = map snd args
  call <- addMeta $ AsmCall resInt fun (zip xs' ts) cont'
  asmCastToInt64 (zip args xs) call

asmCastToInt64 :: [(DataPlus, Identifier)] -> Asm -> WithEnv Asm
asmCastToInt64 [] asm = return asm
asmCastToInt64 (((from, Value fromType), to):rest) asm = do
  asm' <- asmCastToInt64 rest asm
  toInt64 (from, fromType) to asm'

toInt64 :: (Data, PreValue) -> Identifier -> Asm -> WithEnv Asm
toInt64 (from, fromType@(_ :< ValueIndex i)) to cont
  | i `elem` intTypeList = do
    int64 <- getInt64Type
    addMeta $ AsmZeroExtend to (from, Value fromType) int64 cont
toInt64 (from, fromType@(_ :< ValueIndex "f32")) to cont = do
  int32 <- getInt32Type
  int64 <- getInt64Type
  tmp <- newNameWith "cast"
  insValueTypeEnv tmp int32
  cont' <- addMeta $ AsmZeroExtend to (DataLocal tmp, int32) int64 cont
  addMeta $ AsmBitcast tmp (from, Value fromType) int32 cont'
toInt64 (from, fromType@(_ :< ValueIndex "f64")) to cont = do
  int64 <- getInt64Type
  addMeta $ AsmBitcast to (from, Value fromType) int64 cont
toInt64 (from, meta :< ValueIndex _) to cont =
  toInt64 (from, meta :< ValueIndex "i64") to cont
toInt64 (from, fromType) to cont = do
  int64 <- getInt64Type
  addMeta $ AsmPointerToInt to (from, Value fromType) int64 cont

asmCastFromInt64 :: [(Identifier, Identifier)] -> Asm -> WithEnv Asm
asmCastFromInt64 [] asm = return asm
asmCastFromInt64 ((from, to):rest) asm = do
  asm' <- asmCastFromInt64 rest asm
  Value targetType <- lookupValueTypeEnv' to
  fromInt64 from (to, targetType) asm'

fromInt64 :: Identifier -> (Identifier, PreValue) -> Asm -> WithEnv Asm
fromInt64 from (to, toType@(_ :< ValueIndex i)) cont
  | i `elem` intTypeList = do
    fromType <- lookupValueTypeEnv' from
    addMeta $ AsmTrunc to (DataLocal from, fromType) (Value toType) cont
fromInt64 from (to, toType@(_ :< ValueIndex "f32")) cont = do
  int32 <- getInt32Type
  tmp <- newNameWith "cast"
  insValueTypeEnv tmp int32
  cont' <- addMeta $ AsmBitcast to (DataLocal tmp, int32) (Value toType) cont
  fromType <- lookupValueTypeEnv' from
  addMeta $ AsmTrunc tmp (DataLocal from, fromType) int32 cont'
fromInt64 from (to, toType@(_ :< ValueIndex "f64")) cont = do
  fromType <- lookupValueTypeEnv' from
  addMeta $ AsmBitcast to (DataLocal from, fromType) (Value toType) cont
fromInt64 from (to, toType) cont = do
  fromType <- lookupValueTypeEnv' from
  addMeta $ AsmIntToPointer to (DataLocal from, fromType) (Value toType) cont

getInt32Type :: WithEnv Value
getInt32Type = do
  meta <- newNameWith "meta"
  return $ Value $ meta :< ValueIndex "i32"

getInt64Type :: WithEnv Value
getInt64Type = do
  meta <- newNameWith "meta"
  return $ Value $ meta :< ValueIndex "i64"
