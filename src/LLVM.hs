module LLVM
  ( toLLVM
  ) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans.Except
import Data.IORef
import Data.List

import Data
import Reduce
import Util

import Control.Comonad.Cofree

import qualified Text.Show.Pretty as Pr

import Debug.Trace

toLLVM :: WithEnv ()
toLLVM = do
  menv <- gets modalEnv
  forM_ menv $ \(name, (args, e)) -> do
    llvm <- llvmCode e
    insLLVMEnv name args llvm

llvmCode :: Comp -> WithEnv LLVM
llvmCode (CompPiElimBoxElim fun args) = do
  f <- newNameWith "fun"
  xs <- mapM (const (newNameWith "arg")) args
  let funPtrType = toFunPtrType args
  cast <- newNameWith "cast"
  llvmDataLet' ((f, fun) : zip xs args) $
    LLVMLet cast (LLVMBitcast (LLVMDataLocal f) voidPtr funPtrType) $
    LLVMCall (LLVMDataLocal cast) (map LLVMDataLocal xs)
llvmCode (CompIndexElim x branchList) = llvmSwitch x branchList
llvmCode (CompSigmaElim v xs e) =
  llvmCodeSigmaElim v (zip xs [0 ..]) (length xs) e
llvmCode (CompConstElim f args) = llvmCodeConstElim f args
llvmCode (CompUpIntro d) = do
  result <- newNameWith "ans"
  llvmDataLet result d $ LLVMReturn $ LLVMDataLocal result
llvmCode (CompUpElim x cont1 cont2) = do
  cont1' <- llvmCode cont1
  cont2' <- llvmCode cont2
  return $ LLVMLet x cont1' cont2'

llvmCodeSigmaElim :: Value -> [(Identifier, Int)] -> Int -> Comp -> WithEnv LLVM
llvmCodeSigmaElim z xis n cont = do
  basePointer <- newNameWith "sigma"
  c <- llvmCodeSigmaElim' basePointer xis n cont
  llvmDataLet basePointer z c

llvmCodeSigmaElim' ::
     Identifier -> [(Identifier, Int)] -> Int -> Comp -> WithEnv LLVM
llvmCodeSigmaElim' _ [] _ cont = llvmCode cont
llvmCodeSigmaElim' basePointer ((x, i):xis) n cont = do
  cont' <- llvmCodeSigmaElim' basePointer xis n cont
  cast <- newNameWith "cast"
  let structPtrType = toStructPtrType [1 .. n]
  loader <- newNameWith "loader"
  return $
    LLVMLet cast (LLVMBitcast (LLVMDataLocal basePointer) voidPtr structPtrType) $
    LLVMLet loader (LLVMGetElementPtr (LLVMDataLocal cast) (i, n)) $
    LLVMLet x (LLVMLoad (LLVMDataLocal loader)) cont'

llvmCodeConstElim :: Constant -> [Identifier] -> WithEnv LLVM
llvmCodeConstElim (ConstantArith lowType@(LowTypeSignedInt _) kind) xs
  | length xs == 2 = do
    x0 <- newNameWith "arg"
    x1 <- newNameWith "arg"
    cast1 <- newNameWith "cast"
    let op1 = LLVMDataLocal cast1
    cast2 <- newNameWith "cast"
    let op2 = LLVMDataLocal cast2
    result <- newNameWith "result"
    llvmStruct [(x0, ValueVar $ head xs), (x1, ValueVar $ xs !! 1)] $
      LLVMLet cast1 (LLVMPointerToInt (LLVMDataLocal x0) voidPtr lowType) $
      LLVMLet cast2 (LLVMPointerToInt (LLVMDataLocal x1) voidPtr lowType) $
      LLVMLet result (LLVMArith (kind, lowType) op1 op2) $
      LLVMIntToPointer (LLVMDataLocal result) lowType voidPtr
llvmCodeConstElim (ConstantArith (LowTypeUnsignedInt i) kind) xs =
  llvmCodeConstElim (ConstantArith (LowTypeSignedInt i) kind) xs
llvmCodeConstElim (ConstantArith (LowTypeFloat i) kind) xs
  | length xs == 2 = do
    x0 <- newNameWith "arg"
    x1 <- newNameWith "arg"
    cast11 <- newNameWith "cast"
    cast12 <- newNameWith "float"
    cast21 <- newNameWith "cast"
    cast22 <- newNameWith "float"
    tmp <- newNameWith "arith"
    result <- newNameWith "result"
    uncast <- newNameWith "uncast"
    let si = LowTypeSignedInt i
    let op = (kind, LowTypeFloat i)
    llvmStruct [(x0, ValueVar $ head xs), (x1, ValueVar $ xs !! 1)] $
      -- cast the first argument from i8* to float
      LLVMLet cast11 (LLVMPointerToInt (LLVMDataLocal x0) voidPtr si) $
      LLVMLet cast12 (LLVMBitcast (LLVMDataLocal cast11) si (LowTypeFloat i)) $
      -- cast the second argument from i8* to float
      LLVMLet cast21 (LLVMPointerToInt (LLVMDataLocal x1) voidPtr si) $
      LLVMLet cast22 (LLVMBitcast (LLVMDataLocal cast21) si (LowTypeFloat i)) $
      -- compute
      LLVMLet tmp (LLVMArith op (LLVMDataLocal cast12) (LLVMDataLocal cast22)) $
      -- cast the result from float to i8*
      LLVMLet uncast (LLVMBitcast (LLVMDataLocal tmp) (LowTypeFloat i) si) $
      LLVMLet result (LLVMIntToPointer (LLVMDataLocal uncast) si voidPtr) $
      LLVMReturn $ LLVMDataLocal result
llvmCodeConstElim _ _ = lift $ throwE "llvmCodeConstElim"

-- `llvmDataLet x d cont` binds the data `d` to the variable `x`, and computes the
-- continuation `cont`.
llvmDataLet :: Identifier -> Value -> LLVM -> WithEnv LLVM
llvmDataLet x (ValueVar y) cont =
  return $ LLVMLet x (LLVMBitcast (LLVMDataLocal y) voidPtr voidPtr) cont
llvmDataLet x (ValueConst y) cont = do
  cenv <- gets modalEnv
  case lookup y cenv of
    Nothing -> lift $ throwE $ "no such global label defined: " ++ y -- FIXME
    Just (args, _) -> do
      let funPtrType = toFunPtrType args
      return $
        LLVMLet x (LLVMBitcast (LLVMDataGlobal y) funPtrType voidPtr) cont
llvmDataLet reg (ValueSigmaIntro ds) cont = do
  xs <- mapM (const $ newNameWith "cursor") ds
  cast <- newNameWith "cast"
  let ts = map (const voidPtr) ds
  let structPtrType = toStructPtrType ds
  cont'' <- setContent cast (length xs) (zip [0 ..] xs) cont
  llvmStruct (zip xs ds) $
    LLVMLet reg (LLVMAlloc ts) $ -- the result of malloc is i8*
    LLVMLet cast (LLVMBitcast (LLVMDataLocal reg) voidPtr structPtrType) cont''
llvmDataLet x (ValueIndexIntro (IndexInteger i) (LowTypeSignedInt j)) cont =
  return $
  LLVMLet x (LLVMIntToPointer (LLVMDataInt i) (LowTypeSignedInt j) voidPtr) cont
llvmDataLet x (ValueIndexIntro (IndexFloat f) (LowTypeFloat j)) cont = do
  cast <- newNameWith "cast"
  let ft = LowTypeFloat j
  let st = LowTypeSignedInt j
  return $
    LLVMLet cast (LLVMBitcast (LLVMDataFloat f) ft st) $
    LLVMLet x (LLVMIntToPointer (LLVMDataLocal cast) st voidPtr) cont
llvmDataLet _ (ValueIndexIntro _ _) _ =
  lift $ throwE "llvmDataLet.ValueIndexIntro"

llvmDataLet' :: [(Identifier, Value)] -> LLVM -> WithEnv LLVM
llvmDataLet' [] cont = return cont
llvmDataLet' ((x, d):rest) cont = do
  cont' <- llvmDataLet' rest cont
  llvmDataLet x d cont'

constructSwitch :: Value -> [(Index, Comp)] -> WithEnv (LLVM, [(Int, LLVM)])
constructSwitch _ [] = lift $ throwE "empty branch"
constructSwitch name ((IndexLabel x, code):rest) = do
  set <- lookupIndexSet x
  case elemIndex x set of
    Nothing -> lift $ throwE $ "no such index defined: " ++ show name
    Just i -> constructSwitch name ((IndexInteger i, code) : rest)
constructSwitch _ ((IndexDefault, code):_) = do
  code' <- llvmCode code
  return (code', [])
constructSwitch name ((IndexInteger i, code):rest) = do
  code' <- llvmCode code
  (defaultCase, caseList) <- constructSwitch name rest
  return (defaultCase, (i, code') : caseList)
constructSwitch _ ((IndexFloat _, _):_) = undefined -- IEEE754 float equality!

llvmSwitch :: Value -> [(Index, Comp)] -> WithEnv LLVM
llvmSwitch name branchList = do
  (defaultCase, caseList) <- constructSwitch name branchList
  tmp <- newNameWith "switch"
  cast <- newNameWith "cast"
  llvmDataLet' [(tmp, name)] $
    LLVMLet
      cast
      (LLVMPointerToInt (LLVMDataLocal tmp) voidPtr (LowTypeSignedInt 64)) $
    LLVMSwitch (LLVMDataLocal cast) defaultCase caseList

setContent :: Identifier -> Int -> [(Int, Identifier)] -> LLVM -> WithEnv LLVM
setContent _ _ [] cont = return cont
setContent basePointer length ((index, dataAtIndex):sizeDataList) cont = do
  cont' <- setContent basePointer length sizeDataList cont
  loader <- newNameWith "loader"
  hole <- newNameWith "tmp"
  let bp = LLVMDataLocal basePointer
  let voidPtrPtr = LowTypePointer voidPtr
  return $
    LLVMLet loader (LLVMGetElementPtr bp (index, length)) $
    LLVMLet
      hole
      (LLVMStore
         (LLVMDataLocal dataAtIndex, voidPtr)
         (LLVMDataLocal loader, voidPtrPtr))
      cont'

llvmStruct :: [(Identifier, Value)] -> LLVM -> WithEnv LLVM
llvmStruct [] cont = return cont
llvmStruct ((x, d):xds) cont = do
  cont' <- llvmStruct xds cont
  llvmDataLet x d cont'

toFunPtrType :: [a] -> LowType
toFunPtrType xs = do
  let funType = LowTypeFunction (map (const voidPtr) xs) voidPtr
  LowTypePointer funType

toStructPtrType :: [a] -> LowType
toStructPtrType xs = do
  let structType = LowTypeStruct $ map (const voidPtr) xs
  LowTypePointer structType
