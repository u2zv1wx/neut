module Asm
  ( asmCode
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

import           Debug.Trace

asmCode :: Code -> WithEnv [Asm]
asmCode (CodeReturn d)
  -- t <- lookupTypeEnv' meta
 = do
  tmp <- newNameWith "tmp"
  -- insTypeEnv tmp t
  asms <- asmData tmp d
  return $ asms ++ [AsmReturn tmp]
asmCode (CodeLet i d cont)
  -- t <- lookupTypeEnv' meta
 = do
  load <- asmData i d
  cont' <- asmCode cont
  return $ load ++ cont'
asmCode (CodeCall x fun args cont) = do
  asmCont <- asmCode cont
  return $ AsmLet x (AsmCall fun args) : asmCont

asmData :: Identifier -> Data -> WithEnv [Asm]
asmData tmp (DataLocal x) = asmCopy (AsmDataLocal x) tmp
asmData tmp (DataGlobal x) = asmCopy (AsmDataGlobal x) tmp
asmData tmp (DataElemAtIndex basePointer idx) =
  return [AsmLet tmp (AsmGetElemPointer basePointer idx)]
asmData tmp (DataInt32 i) = asmCopy (AsmDataInt32 i) tmp
asmData tmp DataNullPtr = undefined
asmData tmp (DataStruct xs) = undefined

foo :: Data -> WithEnv AsmData
foo (DataLocal x)                     = return $ AsmDataLocal x
foo (DataGlobal x)                    = return $ AsmDataGlobal x
foo (DataElemAtIndex basePointer idx) = undefined --return $ AsmGetElemPointer basePointer idx
foo (DataInt32 i)                     = return $ AsmDataInt32 i
foo DataNullPtr                       = return AsmDataNullPtr
foo (DataStruct xs)                   = return $ AsmDataStruct xs

-- temporary
asmCopy :: AsmData -> Identifier -> WithEnv [Asm]
asmCopy from to = do
  undefined
  -- t <- lookupTypeEnv' to
  -- t' <- unwrapDown t
  -- return [AsmLet to (AsmAlloc t'), AsmStore from to]
