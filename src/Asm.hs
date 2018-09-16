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
  reg <- lookupRegEnv' i
  asmData reg d cont'
asmCode (meta :< CodeCall _ fun _ cont) = do
  let lvs = codeMetaLive meta
  cont' <- asmCode cont
  funReg <- lookupRegEnv' fun
  return $ stackSave lvs $ AsmCall funReg $ stackRestore lvs cont'
asmCode (_ :< CodeExtractValue x base i cont) = do
  t <- lookupPolTypeEnv' base
  case t of
    Pos (_ :< PosExists args _) -> do
      let ts = map snd args
      is <- mapM sizeOfType ts
      let offset = sum $ take i is
      base' <- lookupRegEnv' base
      cont' <- asmCode cont
      return $ AsmLea x ("[" ++ base' ++ " + " ++ show offset ++ "]") cont'
    _ -> lift $ throwE "Asm.asmCode : typeError"
asmCode (_ :< CodeStackSave x cont) = do
  cont' <- asmCode cont
  reg <- lookupRegEnv' x
  return $ AsmPush reg cont'
asmCode (_ :< CodeStackRestore x cont) = do
  cont' <- asmCode cont
  reg <- lookupRegEnv' x
  return $ AsmPop reg cont'

asmData :: Identifier -> Data -> Asm -> WithEnv Asm
asmData reg (DataLocal x) cont = do
  x' <- lookupRegEnv' x
  return $ AsmMov reg x' cont --asmCopy (AsmDataLocal x) reg
asmData reg (DataLabel x) cont = do
  return $ AsmMov reg x cont
asmData reg (DataInt32 i) cont = return $ AsmMov reg (show i) cont
asmData reg (DataStruct xs) cont = do
  is <- mapM sizeOf xs
  let size = sum is
  undefined

stackSave :: [Identifier] -> Asm -> Asm
stackSave xs asm = foldr AsmPush asm xs

stackRestore :: [Identifier] -> Asm -> Asm
stackRestore xs asm = foldr AsmPop asm xs

sizeOf :: Identifier -> WithEnv Int
sizeOf x = do
  Pos t <- lookupPolTypeEnv' x
  sizeOfType t

sizeOfType :: PrePos -> WithEnv Int
sizeOfType = undefined
