module Reduce.LLVM
  ( reduceLLVM,
  )
where

import Control.Monad.State.Lazy
import Data.Basic
import Data.Env
import qualified Data.IntMap as IntMap
import Data.LLVM
import qualified Data.Map as Map
import qualified Data.Set as S

type SizeMap = Map.Map SizeInfo [(Int, LLVMData)]

reduceLLVM :: SubstLLVM -> SizeMap -> LLVM -> WithEnv LLVM
reduceLLVM sub sizeMap llvm =
  case llvm of
    LLVMReturn d ->
      return $ LLVMReturn $ substLLVMData sub d
    -- reduceLLVM sub _ (LLVMReturn d) = return $ LLVMReturn $ substLLVMData sub d
    (LLVMLet x (LLVMOpBitcast d from to) cont)
      | from == to -> do
        let sub' = IntMap.insert (asInt x) (substLLVMData sub d) sub
        reduceLLVM sub' sizeMap cont
    (LLVMLet x (LLVMOpAlloc _ (LowTypePtr (LowTypeArray 0 _))) cont) -> do
      let sub' = IntMap.insert (asInt x) LLVMDataNull sub
      reduceLLVM sub' sizeMap cont
    (LLVMLet x (LLVMOpAlloc _ (LowTypePtr (LowTypeStruct []))) cont) -> do
      let sub' = IntMap.insert (asInt x) LLVMDataNull sub
      reduceLLVM sub' sizeMap cont
    (LLVMLet x op@(LLVMOpAlloc _ size) cont) ->
      case Map.lookup size sizeMap of
        Just ((j, d) : rest) -> do
          modify (\env -> env {nopFreeSet = S.insert j (nopFreeSet env)})
          let sizeMap' = Map.insert size rest sizeMap
          let sub' = IntMap.insert (asInt x) (substLLVMData sub d) sub
          reduceLLVM sub' sizeMap' cont
        _ -> do
          b <- isAlreadyDefined x
          if b
            then do
              x' <- newNameWith x
              let sub' = IntMap.insert (asInt x) (LLVMDataLocal x') sub
              insVar x'
              cont' <- reduceLLVM sub' sizeMap cont
              return $ LLVMLet x' op cont'
            else do
              insVar x
              cont' <- reduceLLVM sub sizeMap cont
              return $ LLVMLet x op cont'
    (LLVMLet x op cont) -> do
      let op' = substLLVMOp sub op
      b <- isAlreadyDefined x
      if b
        then do
          x' <- newNameWith x
          let sub' = IntMap.insert (asInt x) (LLVMDataLocal x') sub
          insVar x'
          cont' <- reduceLLVM sub' sizeMap cont
          return $ LLVMLet x' op' cont'
        else do
          insVar x
          cont' <- reduceLLVM sub sizeMap cont
          return $ LLVMLet x op' cont'
    (LLVMCont op@(LLVMOpFree d size j) cont) -> do
      let op' = substLLVMOp sub op
      let sizeMap' = Map.insertWith (++) size [(j, d)] sizeMap
      cont' <- reduceLLVM sub sizeMap' cont
      return $ LLVMCont op' cont'
    (LLVMCont op cont) -> do
      let op' = substLLVMOp sub op
      cont' <- reduceLLVM sub sizeMap cont
      return $ LLVMCont op' cont'
    (LLVMSwitch (d, t) defaultBranch les) -> do
      let d' = substLLVMData sub d
      let (ls, es) = unzip les
      defaultBranch' <- reduceLLVM sub sizeMap defaultBranch
      es' <- mapM (reduceLLVM sub sizeMap) es
      return $ LLVMSwitch (d', t) defaultBranch' (zip ls es')
    (LLVMBranch d onTrue onFalse) -> do
      let d' = substLLVMData sub d
      onTrue' <- reduceLLVM sub sizeMap onTrue
      onFalse' <- reduceLLVM sub sizeMap onFalse
      return $ LLVMBranch d' onTrue' onFalse'
    (LLVMCall d ds) -> do
      let d' = substLLVMData sub d
      let ds' = map (substLLVMData sub) ds
      return $ LLVMCall d' ds'
    LLVMUnreachable ->
      return LLVMUnreachable

isAlreadyDefined :: Ident -> WithEnv Bool
isAlreadyDefined x = do
  set <- gets defVarSet
  return $ S.member (asInt x) set

insVar :: Ident -> WithEnv ()
insVar x = modify (\env -> env {defVarSet = S.insert (asInt x) (defVarSet env)})
