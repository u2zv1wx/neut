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
  t <- lookupLowTypeEnv' x
  let t' = traceType [0] t
  headTmp <- newNameWith $ x ++ ".elem0"
  let headItemType = (traceType [0, 0] t)
  insLowTypeEnv headTmp $ LowTypePointer headItemType
  loadHead <- newNameWith "tmp"
  insLowTypeEnv loadHead headItemType
  return $
    AsmLet headTmp (AsmGetElemPointer t' x [0]) $
    AsmLet loadHead (AsmLoad headItemType headTmp) $
    AsmSwitch loadHead defaultBranch branchList
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
  let t' = traceType [0] t
  return $ AsmLet x (AsmLoad t' y) asmCont
traceAsm x d@(Fix (DataCell _ i args)) asmCont = do
  t <- typeOfData d
  let t' = traceType [0] t
  let f asm (index, arg) = do
        tmpVar <- newNameWith $ x ++ ".tmpelem" ++ show index
        let itemType = traceType [0, index] t
        insLowTypeEnv tmpVar itemType
        cursor <- newNameWith $ x ++ ".elem" ++ show index
        traceAsm tmpVar arg $
          AsmLet cursor (AsmGetElemPointer t' x [index]) $
          AsmStore itemType (AsmDataRegister tmpVar) cursor asm
  tmp <- foldM f asmCont (zip [1 ..] args)
  headTmp <- newNameWith $ x ++ ".elem0"
  let headItemType = (traceType [0, 0] t)
  insLowTypeEnv headTmp headItemType
  return $
    AsmLet x (AsmAlloc (traceType [0] t)) $
    AsmLet headTmp (AsmGetElemPointer t' x [0]) $
    AsmStore headItemType (AsmDataInt i) headTmp $ tmp
traceAsm x (Fix (DataLabel s)) asmCont = do
  return $
    AsmLet x (AsmAlloc LowTypeLabel) $
    AsmStore LowTypeLabel (AsmDataRegister s) x asmCont
traceAsm x (Fix (DataElemAtIndex baseData idx)) asmCont = do
  tmpVar <- newNameWith "tmp"
  baseType <- typeOfData baseData
  insLowTypeEnv tmpVar baseType
  traceAsm tmpVar baseData $
    AsmLet x (AsmGetElemPointer baseType tmpVar idx) asmCont

typeOfData :: UData -> WithEnv LowType
typeOfData (Fix (DataPointer x)) = do
  tmp <- lookupLowTypeEnv' x
  return tmp
typeOfData (Fix (DataCell _ _ ds)) = do
  ts <- mapM typeOfData ds
  return $ LowTypePointer $ LowTypeStruct $ LowTypeInt32 : ts
typeOfData (Fix (DataLabel _)) = return $ LowTypeLabel
typeOfData (Fix (DataElemAtIndex d idx)) = do
  t <- typeOfData d
  return $ traceType idx t

traceType :: Index -> LowType -> LowType
traceType [] t                      = t
traceType (i:is) (LowTypeStruct ts) = traceType is (ts !! i)
traceType (0:is) (LowTypePointer t) = traceType is t
traceType _ _                       = LowTypeNull
  -- error $ "traceType: index " ++ show i ++ " is out of range for " ++ show t
