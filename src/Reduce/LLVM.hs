module Reduce.LLVM
  ( reduceLLVM
  ) where

import Control.Monad.State

import qualified Data.Map as Map
import qualified Data.Set as S

import Data.Basic
import Data.Env
import Data.LLVM

type SizeMap = Map.Map SizeInfo [(Int, LLVMData)]

reduceLLVM :: SubstLLVM -> SizeMap -> LLVM -> WithEnv LLVM
reduceLLVM sub _ (LLVMReturn d) = do
  let d' = substLLVMData sub d
  return $ LLVMReturn d'
reduceLLVM sub sm (LLVMLet x (LLVMOpBitcast d from to) cont)
  | from == to = reduceLLVM ((asInt x, substLLVMData sub d) : sub) sm cont
reduceLLVM sub sm (LLVMLet x (LLVMOpAlloc _ (LowTypePtr (LowTypeArray 0 _))) cont) = do
  reduceLLVM ((asInt x, LLVMDataNull) : sub) sm cont
reduceLLVM sub sm (LLVMLet x (LLVMOpAlloc _ (LowTypePtr (LowTypeStruct []))) cont) = do
  reduceLLVM ((asInt x, LLVMDataNull) : sub) sm cont
reduceLLVM sub sm (LLVMLet x op@(LLVMOpAlloc _ size) cont) = do
  case Map.lookup size sm of
    Just ((j, d):rest) -> do
      modify (\env -> env {nopFreeSet = S.insert j (nopFreeSet env)})
      let sm' = Map.insert size rest sm
      reduceLLVM ((asInt x, substLLVMData sub d) : sub) sm' cont
    _ -> do
      cont' <- reduceLLVM sub sm cont
      return $ LLVMLet x op cont'
reduceLLVM sub sm (LLVMLet x op cont) = do
  let op' = substLLVMOp sub op
  cont' <- reduceLLVM sub sm cont
  return $ LLVMLet x op' cont'
reduceLLVM sub sm (LLVMCont op@(LLVMOpFree d size j) cont) = do
  let op' = substLLVMOp sub op
  let sm' = Map.insertWith (++) size [(j, d)] sm
  cont' <- reduceLLVM sub sm' cont
  return $ LLVMCont op' cont'
reduceLLVM sub sm (LLVMCont op cont) = do
  let op' = substLLVMOp sub op
  cont' <- reduceLLVM sub sm cont
  return $ LLVMCont op' cont'
reduceLLVM sub sm (LLVMSwitch (d, t) defaultBranch les) = do
  let d' = substLLVMData sub d
  let (ls, es) = unzip les
  defaultBranch' <- reduceLLVM sub sm defaultBranch
  es' <- mapM (reduceLLVM sub sm) es
  return $ LLVMSwitch (d', t) defaultBranch' (zip ls es')
reduceLLVM sub sm (LLVMBranch d onTrue onFalse) = do
  let d' = substLLVMData sub d
  onTrue' <- reduceLLVM sub sm onTrue
  onFalse' <- reduceLLVM sub sm onFalse
  return $ LLVMBranch d' onTrue' onFalse'
reduceLLVM sub _ (LLVMCall d ds) = do
  let d' = substLLVMData sub d
  let ds' = map (substLLVMData sub) ds
  return $ LLVMCall d' ds'
reduceLLVM _ _ LLVMUnreachable = return LLVMUnreachable
