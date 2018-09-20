module Asm
  ( asmCodeEnv
  , asmCode
  ) where

import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.IORef

import           Data
import           Register

import           Control.Comonad.Cofree

import qualified Text.Show.Pretty           as Pr

import           Debug.Trace

asmCodeEnv :: WithEnv ()
asmCodeEnv = do
  env <- get
  forM_ (codeEnv env) $ \(name, (args, codeRef)) -> do
    code <- liftIO $ readIORef codeRef
    argRegList <- getArgRegList
    asm <- asmCode code
    asm' <- bindArgs (zip args argRegList) asm
    insAsmEnv name asm'
    regAlloc 15 asm' -- rsp is not used
    -- insAsmEnv name args asm

asmCode :: Code -> WithEnv Asm
asmCode (CodeReturn d) = do
  tmp <- newNameWith "tmp"
  ret <- addMeta $ AsmReturn tmp
  asmData tmp d ret
asmCode (CodeLet i d cont) = do
  cont' <- asmCode cont
  asmData i d cont'
asmCode (CodeCall x fun args cont) = do
  cont' <- asmCode cont
  if length args > 6
    then lift $ throwE "Asm.asmCode: the number of arguments exceeds 6"
    else asmCodeCall x fun args cont'
  -- addMeta $ AsmCall x fun args cont'
asmCode (CodeExtractValue x base i cont) = do
  t <- lookupTypeEnv' base
  case t of
    _ :< NeutSigma _ _ -> do
      (_, args) <- toSigmaSeq t
      ts <- mapM (toLowType . snd) args
      cont' <- asmCode cont
      addMeta $ AsmExtractValue x (base, ts) i cont'
    _ -> lift $ throwE "Asm.asmCode : typeError"

asmData :: Identifier -> Data -> Asm -> WithEnv Asm
asmData reg (DataLocal x) cont = addMeta $ AsmLet reg (AsmArgReg x) cont
asmData reg (DataLabel x) cont = addMeta $ AsmLet reg (AsmArgLabel x) cont
asmData reg (DataInt32 i) cont = addMeta $ AsmLet reg (AsmArgImmediate i) cont
asmData reg (DataStruct xs) cont = do
  ts <- mapM (lookupTypeEnv' >=> toLowType) xs
  sizeList <- mapM sizeOf xs
  let structSize = sum sizeList
  cont' <- setContent (reg, ts) (zip [0 ..] xs) cont
  rdi <- getRDI
  callThenCont <- asmCodeCall reg "_malloc" [rdi] cont'
  addMeta $ AsmLet rdi (AsmArgImmediate structSize) callThenCont

setContent ::
     (Identifier, [LowType]) -> [(Int, Identifier)] -> Asm -> WithEnv Asm
setContent _ [] cont = return cont
setContent basePointer ((index, dataAtIndex):sizeDataList) cont = do
  cont' <- setContent basePointer sizeDataList cont
  addMeta $ AsmInsertValue (AsmArgReg dataAtIndex) basePointer index cont'

asmCodeCall :: Identifier -> Identifier -> [Identifier] -> Asm -> WithEnv Asm
asmCodeCall x fun args cont = do
  argRegList <- getArgRegList
  rax <- getRAX
  cont' <- addMeta $ AsmLet x (AsmArgReg rax) cont
  call <- addMeta $ AsmCall rax fun args cont'
  bindArgs (zip argRegList args) call

bindArgs :: [(Identifier, Identifier)] -> Asm -> WithEnv Asm
bindArgs [] asm = return asm
bindArgs ((to, from):rest) asm = do
  asm' <- bindArgs rest asm
  addMeta $ AsmLet to (AsmArgReg from) asm'
