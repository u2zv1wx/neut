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
asmCode (CodeReturn d) = do
  x <- newName
  tmp <- addMeta $ AsmReturn x
  asmData x d tmp
asmCode (CodeLet i d cont) = do
  cont' <- asmCode cont
  asmData i d cont'
asmCode (CodeCall x fun args cont) = do
  cont' <- asmCode cont
  if length args > 6
    then lift $ throwE "Asm.asmCode: the number of arguments exceeds 6"
    else do
      argRegList <- getArgRegList
      rax <- getRAX
      cont'' <- addMeta $ AsmMov x rax cont'
      call <- addMeta $ AsmCall rax fun args cont''
      bindArgs (zip args argRegList) call
asmCode (CodeExtractValue x base i cont) = do
  t <- lookupPolTypeEnv' base
  case t of
    Pos (_ :< PosSigma args _) -> do
      let ts = map snd args
      is <- mapM sizeOfType ts
      let offset = sum $ take i is
      cont' <- asmCode cont
      addMeta $ AsmLoadAddr x (AddrAdd (AddrReg base) (AddrInt offset)) cont'
    _ -> lift $ throwE "Asm.asmCode : typeError"

bindArgs :: [(Identifier, Identifier)] -> Asm -> WithEnv Asm
bindArgs [] asm = return asm
bindArgs ((arg, argReg):rest) asm = do
  asm' <- bindArgs rest asm
  addMeta $ AsmMov argReg arg asm'

asmData :: Identifier -> Data -> Asm -> WithEnv Asm
asmData reg (DataLocal x) cont = addMeta $ AsmMov reg x cont
asmData reg (DataLabel x) cont = addMeta $ AsmMov reg x cont
asmData reg (DataInt32 i) cont = addMeta $ AsmMov reg (show i) cont
asmData reg (DataStruct xs) cont = do
  is <- mapM sizeOf xs
  let size = sum is
  -- mallocしてregにpointerをとって、んで要素をsetしてからcont'を続ける、とかで。
  undefined

sizeOf :: Identifier -> WithEnv Int
sizeOf x = do
  Pos t <- lookupPolTypeEnv' x
  sizeOfType t

sizeOfType :: PrePos -> WithEnv Int
sizeOfType = undefined
