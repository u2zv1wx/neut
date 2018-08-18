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
asmCode (CodeReturn d) = do
  tmp <- newNameWith "tmp"
  t <- typeOfData d
  insLowTypeEnv tmp $ LowTypePointer t
  tmpAsm <- traceAsm tmp d
  return $ tmpAsm ++ [AsmReturn (tmp, LowTypePointer t)]
asmCode (CodeSwitch basePointer defaultBranch branchList) = do
  baseType <- lookupLowTypeEnv' basePointer
  cursorAt00 <- newNameWith $ basePointer ++ ".cursor0"
  let dataType = traceType [0, 0] baseType
  headData <- newNameWith $ basePointer ++ ".kind"
  insLowTypeEnv headData $ dataType
  insLowTypeEnv cursorAt00 $ LowTypePointer dataType
  return $
    [ AsmLet cursorAt00 (AsmGetElemPointer baseType basePointer [0, 0])
    , AsmLet headData (AsmLoad (LowTypePointer dataType) cursorAt00)
    , AsmSwitch headData defaultBranch branchList
    ]
asmCode (CodeJump label) = return [AsmBranch label]
asmCode (CodeIndirectJump x unthunkId poss) = do
  labelList <-
    forM poss $ \thunkId -> do
      return $ "thunk" ++ thunkId ++ "unthunk" ++ unthunkId
  return [AsmIndirectBranch x labelList]
asmCode (CodeRecursiveJump x) = return [AsmIndirectBranch x [x]]
asmCode (CodeLet i d cont) = do
  t <- typeOfData d
  insLowTypeEnv i $ LowTypePointer t
  cont' <- asmCode cont
  tmp <- traceAsm i d
  return $ tmp ++ cont'
asmCode (CodeWithArg xds code) = do
  let (xs, ds) = unzip xds
  tmp <- letSeq xs ds code
  asmCode tmp
asmCode (CodeCall x name args cont)
  -- bind all arguments using traceasm and then call name
 = do
  undefined

traceAsm :: Identifier -> Data -> WithEnv [Asm]
traceAsm x (DataPointer y) = do
  ty <- lookupLowTypeEnv' y
  return [AsmLet x (AsmAlloc ty), AsmStore ty (AsmDataRegister y) x]
traceAsm x d@(DataCell _ i args) = do
  let args' = (DataInt32 i) : args
  t <- typeOfData d
  tmp <- join <$> (forM (zip [0 ..] args') $ setIthData x)
  return $ AsmLet x (AsmAlloc t) : tmp
traceAsm x (DataLabel s) = do
  let labelPointerType = LowTypePointer (LowTypeInt8)
  return $
    [ AsmLet x (AsmAlloc labelPointerType)
    , AsmStore labelPointerType (AsmDataLabel s) x
    ]
traceAsm x (DataElemAtIndex basePointer idx) = do
  baseType <- lookupLowTypeEnv' basePointer
  return
    [AsmLet x (AsmGetElemPointer baseType basePointer (0 : modifyIndex idx))]
traceAsm x d@(DataInt32 i) = do
  baseType <- typeOfData d -- i32*
  return [AsmLet x (AsmAlloc baseType), AsmStore baseType (AsmDataInt i) x]

traceAsm' :: Identifier -> Data -> WithEnv [Asm]
traceAsm' x (DataPointer y) = do
  ty <- lookupLowTypeEnv' y
  return [AsmStore ty (AsmDataRegister y) x]
traceAsm' x (DataCell _ i args) = do
  let args' = (DataInt32 i) : args
  join <$> (forM (zip [0 ..] args') $ setIthData x)
traceAsm' x (DataLabel s) = do
  return [AsmStore LowTypeLabel (AsmDataRegister s) x]
traceAsm' x (DataElemAtIndex basePointer idx) = do
  baseType <- lookupLowTypeEnv' basePointer
  return
    [AsmLet x (AsmGetElemPointer baseType basePointer (0 : modifyIndex idx))]
traceAsm' x d@(DataInt32 i) = do
  baseType <- typeOfData d -- i32*
  return [AsmStore baseType (AsmDataInt i) x]

setIthData :: Identifier -> (Int, Data) -> WithEnv [Asm]
setIthData x (index, ithArg) = do
  ithCursor <- newNameWith $ x ++ ".cursor" ++ show index
  td <- typeOfData ithArg
  xt <- lookupLowTypeEnv' x
  insLowTypeEnv ithCursor (LowTypePointer td)
  asm <- traceAsm' ithCursor ithArg
  return $ AsmLet ithCursor (AsmGetElemPointer xt x [0, index]) : asm

typeOfData :: Data -> WithEnv LowType
typeOfData (DataPointer x) = lookupLowTypeEnv' x
typeOfData (DataCell _ _ ds) = do
  ts <- mapM typeOfData ds
  return $ LowTypeStruct $ LowTypeInt32 : ts
typeOfData (DataLabel _) = return LowTypeLabel
typeOfData (DataElemAtIndex basePointer idx) = do
  t <- lookupLowTypeEnv' basePointer
  return $ traceType (0 : modifyIndex idx) t
typeOfData (DataInt32 _) = return LowTypeInt32

traceType :: Index -> LowType -> LowType
traceType [] t = t
traceType (i:is) (LowTypeStruct ts) =
  if 0 <= i && i < length ts
    then traceType is (ts !! i)
    else LowTypeNull
traceType (0:is) (LowTypePointer t) = traceType is t
traceType _ _ = LowTypeNull -- quit process and emit "ret void"

-- the first element of an inductive value is kind (i32)
modifyIndex :: Index -> Index
modifyIndex index = map (\i -> i + 1) index
