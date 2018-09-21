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
    initRegVar
    asm <- asmCode code
    asm' <- bindArgs (zip args argRegList) asm
    insAsmEnv name asm'
    liftIO $ putStrLn $ Pr.ppShow asm'
    regAlloc 15 asm' -- rsp is not used
    -- insAsmEnv name args asm

asmCode :: Code -> WithEnv Asm
asmCode (CodeReturn d) = do
  rax <- getRAX
  tmp <- addMeta $ AsmReturn rax
  asmData rax d tmp
  -- tmp <- newNameWith "tmp"
  -- ret <- addMeta $ AsmReturn tmp
  -- asmData tmp d ret
asmCode (CodeLet i d cont) = do
  cont' <- asmCode cont
  asmData i d cont'
asmCode (CodeCall x fun args cont) = do
  cont' <- asmCode cont
  if length args > 6
    then lift $ throwE "Asm.asmCode: the number of arguments exceeds 6"
    else asmCodeCall x fun args cont'
  -- addMeta $ AsmCall x fun args cont'
asmCode (CodeSwitch x branchList) = asmSwitch x branchList
asmCode (CodeExtractValue x base i cont) = do
  t <- lookupTypeEnv' base
  case t of
    _ :< NeutSigma _ _ -> do
      (_, args) <- toSigmaSeq t
      ts <- mapM (toLowType . snd) args
      let offset = sum $ map sizeOfLowType $ take i ts
      cont' <- asmCode cont
      addMeta $ AsmExtractValue x base offset cont'
    _ -> lift $ throwE "Asm.asmCode : typeError"

asmData :: Identifier -> Data -> Asm -> WithEnv Asm
asmData reg (DataLocal x) cont = addMeta $ AsmLet reg (AsmArgReg x) cont
asmData reg (DataLabel x) cont = addMeta $ AsmLet reg (AsmArgLabel x) cont
asmData reg (DataInt32 i) cont = addMeta $ AsmLet reg (AsmArgImmediate i) cont
asmData reg (DataStruct xs) cont = do
  sizeList <- mapM sizeOf xs
  let structSize = sum sizeList
  cont' <- setContent reg sizeList (zip [0 ..] xs) cont
  rdi <- getRDI
  callThenCont <- asmCodeCall reg "_malloc" [rdi] cont'
  addMeta $ AsmLet rdi (AsmArgImmediate structSize) callThenCont

asmSwitch :: Identifier -> [(Int, Code)] -> WithEnv Asm
asmSwitch _ [] = lift $ throwE "empty branch"
asmSwitch _ [(index, code)] = do
  asm <- asmCode code
  x <- newNameWith "case"
  let label = x ++ "." ++ show index
  insAsmEnv label asm
  addMeta $ AsmJump label
asmSwitch name ((index, code):rest) = do
  cont <- asmSwitch name rest
  asm <- asmCode code
  x <- newNameWith "case"
  let label = x ++ "." ++ show index
  insAsmEnv label asm
  cont' <- addMeta $ AsmJumpIfZero label cont
  addMeta $ AsmCompare name label cont'

setContent :: Identifier -> [Int] -> [(Int, Identifier)] -> Asm -> WithEnv Asm
setContent _ _ [] cont = return cont
setContent basePointer sizeList ((i, dataAtIndex):sizeDataList) cont = do
  cont' <- setContent basePointer sizeList sizeDataList cont
  let offset = sum $ take i sizeList
  addMeta $ AsmInsertValue (AsmArgReg dataAtIndex) basePointer offset cont'

asmCodeCall :: Identifier -> Identifier -> [Identifier] -> Asm -> WithEnv Asm
asmCodeCall x fun args cont = do
  argRegList <- getArgRegList
  rax <- getRAX
  cont' <- addMeta $ AsmLet x (AsmArgReg rax) cont
  call <- addMeta $ AsmCall rax (AsmArgReg fun) args cont'
  bindArgs (zip argRegList args) call

bindArgs :: [(Identifier, Identifier)] -> Asm -> WithEnv Asm
bindArgs [] asm = return asm
bindArgs ((to, from):rest) asm = do
  asm' <- bindArgs rest asm
  addMeta $ AsmLet to (AsmArgReg from) asm'
