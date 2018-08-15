module Asm where

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

asmEmit :: WithEnv ()
asmEmit = do
  env <- get
  -- liftIO $ putStrLn "define void @main() {"
  -- exitLabel <- newNameWith "exit"
  forM_ (funEnv env) $ \(_, codeRef) -> do
    code <- liftIO $ readIORef codeRef
    asm <- asmCode code
    liftIO $ putStrLn $ Pr.ppShow asm
  -- emitLabelHeader "exit"
  -- emitOp $ "ret void"
  -- liftIO $ putStrLn "}"

asmCode :: Code -> WithEnv Asm
asmCode (CodeMeta {codeMetaArgs = xds@(_:_)} :< code) = do
  let (xs, ds) = unzip xds
  code' <- addMeta code
  tmp <- letSeq xs ds code'
  asmCode tmp
asmCode (meta :< CodeReturn retReg label d) = do
  tmp <- addMeta $ CodeJump label
  asmCode $ meta :< CodeLet retReg d tmp
asmCode (meta :< CodeLetLink i d cont) = do
  asmCode $ meta :< CodeLet i d cont
asmCode (_ :< CodeSwitch x defaultBranch branchList) = do
  return $ AsmSwitch x defaultBranch branchList
asmCode (_ :< CodeJump label) = return $ AsmBranch label
asmCode (_ :< CodeIndirectJump x unthunkId poss) = do
  labelList <-
    forM poss $ \thunkId -> do
      return $ "thunk" ++ thunkId ++ "unthunk" ++ unthunkId
  return $ AsmIndirectBranch x labelList
asmCode (_ :< CodeRecursiveJump x) = return $ AsmIndirectBranch x [x]
asmCode (_ :< CodeStackSave stackReg cont) = do
  asmCont <- asmCode cont
  return $ AsmLet stackReg AsmStackSave asmCont
asmCode (_ :< CodeStackRestore stackReg cont) = do
  asmCont <- asmCode cont
  return $ AsmLet stackReg AsmStackRestore asmCont
asmCode (_ :< CodeLet i d cont) = do
  t <- typeOfData d
  insLowTypeEnv i t
  cont' <- asmCode cont
  traceAsm i d cont'

-- let x := d in asmCont
traceAsm :: Identifier -> UData -> Asm -> WithEnv Asm
traceAsm x d@(Fix (DataPointer y)) asmCont = do
  t <- typeOfData d
  return $ AsmLet x (AsmLoad t y) asmCont
traceAsm x d@(Fix (DataCell _ args)) asmCont = do
  t <- typeOfData d
  let f asm (index, arg) = do
        tmpVar <- newNameWith "tmp"
        let itemType = traceType [index] t
        insLowTypeEnv tmpVar itemType
        traceAsm tmpVar arg $ AsmStore itemType tmpVar x asm
  tmp <- foldM f asmCont (zip [1 ..] args)
  return $ AsmLet x (AsmAlloc t) $ tmp
traceAsm x (Fix (DataLabel s)) asmCont = do
  return $ AsmLet x (AsmAlloc LowTypeLabel) $ AsmStore LowTypeLabel s x asmCont
traceAsm x (Fix (DataElemAtIndex baseData idx)) asmCont = do
  tmpVar <- newNameWith "tmp"
  baseType <- typeOfData baseData
  insLowTypeEnv tmpVar baseType
  traceAsm tmpVar baseData $
    AsmLet x (AsmGetElemPointer baseType tmpVar idx) asmCont

typeOfData :: UData -> WithEnv LowType
typeOfData (Fix (DataPointer x)) = lookupLowTypeEnv' x
typeOfData (Fix (DataCell _ ds)) = do
  ts <- mapM typeOfData ds
  return $ LowTypeStruct $ LowTypeInt32 : map LowTypePointer ts
typeOfData (Fix (DataLabel _)) = return $ LowTypeLabel
typeOfData (Fix (DataElemAtIndex d idx)) = do
  t <- typeOfData d
  return $ traceType idx t

traceType :: Index -> LowType -> LowType
traceType [] t                      = t
traceType (i:is) (LowTypeStruct ts) = traceType is (ts !! (i - 1))
traceType (i:is) (LowTypePointer t) = traceType (i : is) t
traceType i t                       = LowTypeNull
  -- error $ "traceType: index " ++ show i ++ " is out of range for " ++ show t
