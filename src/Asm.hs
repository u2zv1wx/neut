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

asmCode :: Code -> WithEnv Asm
asmCode (_ :< CodeReturn d) = asmData "%rax" d AsmReturn
asmCode (_ :< CodeLet i d cont) = do
  cont' <- asmCode cont
  asmData i d cont'
asmCode (meta :< CodeCall _ fun _ cont) = do
  let lvs = codeMetaLive meta
  cont' <- asmCode cont
  return $ stackSave lvs $ AsmCall fun $ stackRestore lvs cont'
asmCode (_ :< CodeExtractValue x base idx cont) = do
  undefined
asmCode (_ :< CodeStackSave x cont) = do
  cont' <- asmCode cont
  return $ AsmPush x cont'
asmCode (_ :< CodeStackRestore x cont) = do
  cont' <- asmCode cont
  return $ AsmPop x cont'

asmData :: Identifier -> Data -> Asm -> WithEnv Asm
asmData tmp (DataLocal x) cont = do
  tmp' <- lookupRegEnv' tmp
  x' <- lookupRegEnv' x
  return $ AsmMov tmp' x' cont --asmCopy (AsmDataLocal x) tmp
asmData tmp (DataLabel x) cont = do
  tmp' <- lookupRegEnv' tmp
  return $ AsmMov tmp' x cont
asmData tmp DataNullPtr cont = undefined
asmData tmp (DataStruct xs) cont = do
  is <- mapM sizeOf xs
  undefined

stackSave :: [Identifier] -> Asm -> Asm
stackSave xs asm = foldr AsmPush asm xs

stackRestore :: [Identifier] -> Asm -> Asm
stackRestore xs asm = foldr AsmPop asm xs

sizeOf :: Identifier -> WithEnv Int
sizeOf = undefined
