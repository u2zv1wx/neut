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
  tmp <- newNameWith "alloc"
  asms <- asmData tmp d
  t <- typeOfData d
  insLowTypeEnv tmp (LowTypePointer t)
  return $ asms ++ [AsmReturn (tmp, LowTypePointer t)]
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
  j <- newNameWith "loader"
  insLowTypeEnv j (LowTypePointer t)
  insLowTypeEnv i t
  asms <- asmData j d
  cont' <- asmCode cont
  return $ asms ++ [AsmLet i (AsmLoad (LowTypePointer t) j)] ++ cont'
asmCode (CodeWithArg xds code) = do
  let (xs, ds) = unzip xds
  tmp <- letSeq xs ds code
  asmCode tmp
asmCode (CodeCall x name args cont) = do
  asms <-
    forM args $ \(ident, d) -> do
      j <- newNameWith "loader"
      td <- typeOfData d
      insLowTypeEnv j (LowTypePointer td)
      insLowTypeEnv ident td
      asms <- asmData j d
      return $ asms ++ [AsmLet ident (AsmLoad (LowTypePointer td) j)]
  cont' <- asmCode cont
  t <- lookupLowTypeEnv' name
  case t of
    LowTypeLabel (LowTypeFunction xts codType) -> do
      let domTypes = map snd xts
      let vars = map fst args
      return $
        join asms ++
        [AsmLet x (AsmCall (name, codType) (zip vars domTypes))] ++ cont'
    _ ->
      lift $ throwE $ "the type of " ++ name ++ " is not a function: " ++ show t

-- allocate data (if needed) and set tmp to be a pointer to the data
asmData :: Identifier -> Data -> WithEnv [Asm]
asmData tmp (DataPointer x) = do
  t <- lookupLowTypeEnv' x
  insLowTypeEnv tmp (LowTypePointer t)
  return [AsmLet tmp (AsmAlloc t), AsmStore t (AsmDataRegister x) tmp]
asmData x d@(DataCell _ i args) = do
  let args' = (DataInt32 i) : args
  t <- typeOfData d
  insLowTypeEnv x (LowTypePointer t)
  tmp <- join <$> (forM (zip [0 ..] args') $ setIthData x)
  return $ AsmLet x (AsmAlloc t) : tmp
asmData tmp (DataLabel x) = do
  let labelPointerType = LowTypePointer LowTypeInt8
  insLowTypeEnv tmp (labelPointerType)
  return
    [ AsmLet tmp (AsmAlloc labelPointerType)
    , AsmStore labelPointerType (AsmDataLabel x) tmp
    ]
asmData tmp (DataElemAtIndex basePointer idx) = do
  baseType <- lookupLowTypeEnv' basePointer
  insLowTypeEnv tmp (LowTypePointer (traceType (0 : modifyIndex idx) baseType))
  return
    [AsmLet tmp (AsmGetElemPointer baseType basePointer (0 : modifyIndex idx))]
asmData tmp d@(DataInt32 i) = do
  baseType <- typeOfData d -- i32*
  insLowTypeEnv tmp (LowTypePointer baseType)
  return [AsmLet tmp (AsmAlloc baseType), AsmStore baseType (AsmDataInt i) tmp]

asmData' :: Identifier -> Data -> WithEnv [Asm]
asmData' x (DataPointer y) = do
  ty <- lookupLowTypeEnv' y
  insLowTypeEnv x (LowTypePointer ty)
  return [AsmStore ty (AsmDataRegister y) x]
asmData' x d@(DataCell _ i args) = do
  let args' = (DataInt32 i) : args
  t <- typeOfData d
  insLowTypeEnv x (LowTypePointer t)
  join <$> (forM (zip [0 ..] args') $ setIthData x)
asmData' x (DataLabel s) = do
  let labelPointerType = LowTypePointer LowTypeInt8
  insLowTypeEnv x (labelPointerType)
  return [AsmStore LowTypeInt8 (AsmDataRegister s) x]
asmData' x (DataElemAtIndex basePointer idx) = do
  baseType <- lookupLowTypeEnv' basePointer
  insLowTypeEnv x (LowTypePointer (traceType (0 : modifyIndex idx) baseType))
  return
    [AsmLet x (AsmGetElemPointer baseType basePointer (0 : modifyIndex idx))]
asmData' x d@(DataInt32 i) = do
  baseType <- typeOfData d -- i32*
  insLowTypeEnv x (LowTypePointer baseType)
  return [AsmStore baseType (AsmDataInt i) x]

setIthData :: Identifier -> (Int, Data) -> WithEnv [Asm]
setIthData x (index, ithArg) = do
  xt <- lookupLowTypeEnv' x
  ithCursor <- newNameWith $ "cursor" ++ show index
  td <- typeOfData ithArg
  insLowTypeEnv ithCursor (LowTypePointer td)
  asms <- asmData' ithCursor ithArg
  return $ AsmLet ithCursor (AsmGetElemPointer xt x [0, index]) : asms

--  asm <- traceAsm' ithCursor ithArg
typeOfData :: Data -> WithEnv LowType
typeOfData (DataPointer x) = lookupLowTypeEnv' x
typeOfData (DataCell _ _ ds) = do
  ts <- mapM typeOfData ds
  return $ LowTypeStruct $ LowTypeInt32 : ts
typeOfData (DataLabel _) = return $ LowTypePointer LowTypeInt8
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
