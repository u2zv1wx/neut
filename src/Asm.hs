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

asmCode :: Code -> WithEnv [Asm]
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
asmCode (_ :< CodeSwitch basePointer defaultBranch branchList) = do
  baseType <- lookupLowTypeEnv' basePointer
  cursorAt00 <- newNameWith $ basePointer ++ ".cursor0"
  let dataType = traceType [0, 0] baseType
  -- let typeAt00 = traceType [0, 0] baseType
  headData <- newNameWith $ basePointer ++ ".kind"
  insLowTypeEnv headData $ dataType
  insLowTypeEnv cursorAt00 $ LowTypePointer dataType
  return $
    [ AsmLet cursorAt00 (AsmGetElemPointer baseType basePointer [0, 0])
    , AsmLet headData (AsmLoad (LowTypePointer dataType) cursorAt00)
    , AsmSwitch headData defaultBranch branchList
    ]
asmCode (_ :< CodeJump label) = return [AsmBranch label]
asmCode (_ :< CodeIndirectJump x unthunkId poss) = do
  labelList <-
    forM poss $ \thunkId -> do
      return $ "thunk" ++ thunkId ++ "unthunk" ++ unthunkId
  return [AsmIndirectBranch x labelList]
asmCode (_ :< CodeRecursiveJump x) = return [AsmIndirectBranch x [x]]
asmCode (_ :< CodeStackSave stackReg cont) = do
  asmCont <- asmCode cont
  return $ AsmLet stackReg AsmStackSave : asmCont
asmCode (_ :< CodeStackRestore stackReg cont) = do
  asmCont <- asmCode cont
  return $ AsmLet stackReg AsmStackRestore : asmCont
asmCode (_ :< CodeLet i d cont) = do
  t <- typeOfData d
  insLowTypeEnv i $ LowTypePointer t
  cont' <- asmCode cont
  tmp <- traceAsm i d
  return $ tmp ++ cont'

traceAsm :: Identifier -> UData -> WithEnv [Asm]
traceAsm x (Fix (DataPointer y)) = do
  ty <- lookupLowTypeEnv' y
  return [AsmLet x (AsmAlloc ty), AsmStore ty (AsmDataRegister y) x]
traceAsm x d@(Fix (DataCell _ i args)) = do
  let args' = Fix (DataInt32 i) : args
  t <- typeOfData d
  tmp <- join <$> (forM (zip [0 ..] args') $ setIthData x)
  return $ AsmLet x (AsmAlloc t) : tmp
traceAsm x (Fix (DataLabel s)) = do
  let labelPointerType = LowTypePointer (LowTypeInt8)
  return $
    [ AsmLet x (AsmAlloc labelPointerType)
    , AsmStore labelPointerType (AsmDataLabel s) x
    ]
traceAsm x (Fix (DataElemAtIndex basePointer idx)) = do
  baseType <- lookupLowTypeEnv' basePointer
  return
    [AsmLet x (AsmGetElemPointer baseType basePointer (0 : modifyIndex idx))]
traceAsm x d@(Fix (DataInt32 i)) = do
  baseType <- typeOfData d -- i32*
  return [AsmLet x (AsmAlloc baseType), AsmStore baseType (AsmDataInt i) x]

traceAsm' :: Identifier -> UData -> WithEnv [Asm]
traceAsm' x (Fix (DataPointer y)) = do
  ty <- lookupLowTypeEnv' y
  return [AsmStore ty (AsmDataRegister y) x]
traceAsm' x (Fix (DataCell _ i args)) = do
  let args' = Fix (DataInt32 i) : args
  join <$> (forM (zip [0 ..] args') $ setIthData x)
traceAsm' x (Fix (DataLabel s)) = do
  return [AsmStore LowTypeLabel (AsmDataRegister s) x]
traceAsm' x (Fix (DataElemAtIndex basePointer idx)) = do
  baseType <- lookupLowTypeEnv' basePointer
  return
    [AsmLet x (AsmGetElemPointer baseType basePointer (0 : modifyIndex idx))]
traceAsm' x d@(Fix (DataInt32 i)) = do
  baseType <- typeOfData d -- i32*
  return [AsmStore baseType (AsmDataInt i) x]

setIthData :: Identifier -> (Int, UData) -> WithEnv [Asm]
setIthData x (index, ithArg) = do
  ithCursor <- newNameWith $ x ++ ".cursor" ++ show index
  td <- typeOfData ithArg
  xt <- lookupLowTypeEnv' x
  insLowTypeEnv ithCursor (LowTypePointer td)
  asm <- traceAsm' ithCursor ithArg
  return $ AsmLet ithCursor (AsmGetElemPointer xt x [0, index]) : asm

typeOfData :: UData -> WithEnv LowType
typeOfData (Fix (DataPointer x)) = lookupLowTypeEnv' x
typeOfData (Fix (DataCell _ _ ds)) = do
  ts <- mapM typeOfData ds
  return $ LowTypeStruct $ LowTypeInt32 : ts
typeOfData (Fix (DataLabel _)) = return LowTypeLabel
typeOfData (Fix (DataElemAtIndex basePointer idx)) = do
  t <- lookupLowTypeEnv' basePointer
  return $ traceType (0 : modifyIndex idx) t
typeOfData (Fix (DataInt32 _)) = return LowTypeInt32

traceType :: Index -> LowType -> LowType
traceType [] t                      = t
traceType (i:is) (LowTypeStruct ts) = traceType is (ts !! i)
traceType (0:is) (LowTypePointer t) = traceType is t
traceType _ _                       = LowTypeNull -- quit process and emit "ret void"

-- the first element of an inductive value is kind (i32)
modifyIndex :: Index -> Index
modifyIndex index = map (\i -> i + 1) index
