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
    initRegVar
    argRegList <- getArgRegList
    asm <- asmCode code
    asm' <- bindArgs (zip args argRegList) asm
    insAsmEnv name asm'
    liftIO $ putStrLn $ Pr.ppShow asm'
    regAlloc 15 asm' -- rsp is not used

asmCode :: Code -> WithEnv Asm
asmCode (CodeReturn d) = do
  rax <- getRAX
  tmp <- addMeta $ AsmReturn rax
  asmData rax d tmp
asmCode (CodeLet i d cont) = do
  cont' <- asmCode cont
  asmData i d cont'
asmCode (CodeCall dest "core.add" [x, y] cont) = do
  cont' <- asmCode cont
  cont'' <- addMeta $ AsmAddInt64 (AsmArgReg y) dest cont'
  addMeta $ AsmLet dest (AsmArgReg x) cont''
asmCode (CodeCall x fun args cont) = do
  cont' <- asmCode cont
  if length args > 6
    then lift $ throwE "Asm.asmCode: the number of arguments exceeds 6"
    else asmCodeCall x fun args cont'
asmCode (CodeSwitch x branchList) = asmSwitch x branchList
asmCode (CodeExtractValue x base i cont) = do
  t <- lookupTypeEnv' base
  case t of
    _ :< NeutSigma xts t -> do
      let args = map snd xts ++ [t]
      ts <- mapM toLowType args
      let offset = sum $ map sizeOfLowType $ take i ts
      cont' <- asmCode cont
      addMeta $ AsmExtractValue x base offset cont'
    _ -> lift $ throwE "Asm.asmCode : typeError"
asmCode (CodeFree x cont) = do
  tmp <- newName
  cont' <- asmCode cont
  asmCodeCall tmp "_free" [x] cont'

asmData :: Identifier -> Data -> Asm -> WithEnv Asm
asmData reg (DataLocal x) cont = addMeta $ AsmLet reg (AsmArgReg x) cont
asmData reg (DataLabel x) cont = addMeta $ AsmLet reg (AsmArgLabel x) cont
asmData reg (DataInt32 i) cont = addMeta $ AsmLet reg (AsmArgImmediate i) cont
asmData reg (DataStruct ds) cont = do
  xs <- mapM (const newName) ds
  let sizeList = map sizeOfData ds
  let structSize = sum sizeList
  cont' <- setContent reg sizeList (zip [0 ..] xs) cont
  rdi <- getRDI
  callThenCont <- asmCodeCall reg "_malloc" [rdi] cont'
  tmp <- addMeta $ AsmLet rdi (AsmArgImmediate structSize) callThenCont
  asmStruct (zip xs ds) tmp

asmStruct :: [(Identifier, Data)] -> Asm -> WithEnv Asm
asmStruct [] cont = return cont
asmStruct ((x, d):xds) cont = do
  cont' <- asmStruct xds cont
  asmData x d cont'

asmSwitch :: Identifier -> [(Index, Code)] -> WithEnv Asm
asmSwitch _ [] = lift $ throwE "empty branch"
asmSwitch _ [(_, code)] = asmSwitchLast code
asmSwitch _ ((IndexDefault, code):_) = asmSwitchLast code
asmSwitch name ((i, code):rest) = do
  cont <- asmSwitch name rest
  asm <- asmCode code
  x <- newNameWith "case"
  let label = x ++ "." ++ showIndex i
  insAsmEnv label asm
  cont' <- addMeta $ AsmJumpIfZero label cont
  addMeta $ AsmCompare name label cont'

asmSwitchLast :: Code -> WithEnv Asm
asmSwitchLast code = do
  asm <- asmCode code
  label <- newNameWith "default"
  insAsmEnv label asm
  addMeta $ AsmJump label

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

showIndex :: Index -> String
showIndex (IndexInteger i) = show i
showIndex (IndexLabel s)   = s
showIndex IndexDefault     = "default"

sizeOfData :: Data -> Int
sizeOfData (DataLocal _)   = 8
sizeOfData (DataLabel x)   = 8
sizeOfData (DataInt32 i)   = 8
sizeOfData (DataStruct ds) = sum $ map sizeOfData ds
