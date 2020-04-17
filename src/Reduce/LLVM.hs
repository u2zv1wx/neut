module Reduce.LLVM
  ( reduceLLVM
  ) where

import Control.Monad.State.Lazy

import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import qualified Data.Set as S

import Data.Basic
import Data.Env
import Data.LLVM

type SizeMap = Map.Map SizeInfo [(Int, LLVMData)]

reduceLLVM :: SubstLLVM -> SizeMap -> LLVM -> WithEnv LLVM
reduceLLVM sub _ (LLVMReturn d) = return $ LLVMReturn $ substLLVMData sub d
-- reduceLLVM sub sm (LLVMLet x (LLVMOpBitcast d from to) cont)
--   | from == to = do
--     let sub' = IntMap.insert (asInt x) (substLLVMData sub d) sub
--     reduceLLVM sub' sm cont
-- reduceLLVM sub sm (LLVMLet x (LLVMOpAlloc _ (LowTypePtr (LowTypeArray 0 _))) cont) = do
--   let sub' = IntMap.insert (asInt x) LLVMDataNull sub
--   reduceLLVM sub' sm cont
-- reduceLLVM sub sm (LLVMLet x (LLVMOpAlloc _ (LowTypePtr (LowTypeStruct []))) cont) = do
--   let sub' = IntMap.insert (asInt x) LLVMDataNull sub
--   reduceLLVM sub' sm cont
-- reduceLLVM sub sm (LLVMLet x op@(LLVMOpAlloc _ size) cont) = do
--   case Map.lookup size sm of
--     Just ((j, d):rest) -> do
--       modify (\env -> env {nopFreeSet = S.insert j (nopFreeSet env)})
--       let sm' = Map.insert size rest sm
--       let sub' = IntMap.insert (asInt x) (substLLVMData sub d) sub
--       reduceLLVM sub' sm' cont
--     _ -> do
--       b <- isAlreadyDefined x
--       if b
--         then do
--           x' <- newNameWith x
--           let sub' = IntMap.insert (asInt x) (LLVMDataLocal x') sub
--           insVar x'
--           cont' <- reduceLLVM sub' sm cont
--           return $ LLVMLet x' op cont'
--         else do
--           insVar x
--           cont' <- reduceLLVM sub sm cont
--           return $ LLVMLet x op cont'
reduceLLVM sub sm (LLVMLet x op cont) = do
  let op' = substLLVMOp sub op
  b <- isAlreadyDefined x
  if b
    then do
      x' <- newNameWith x
      let sub' = IntMap.insert (asInt x) (LLVMDataLocal x') sub
      insVar x'
      cont' <- reduceLLVM sub' sm cont
      return $ LLVMLet x' op' cont'
    else do
      insVar x
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

isAlreadyDefined :: Identifier -> WithEnv Bool
isAlreadyDefined x = do
  set <- gets defVarSet
  return $ S.member (asInt x) set

insVar :: Identifier -> WithEnv ()
insVar x = modify (\env -> env {defVarSet = S.insert (asInt x) (defVarSet env)})
