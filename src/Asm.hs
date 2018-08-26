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

asmCode :: Code -> WithEnv [Asm]
asmCode (CodeReturn d@(meta :< _)) = do
  t <- lookupTypeEnv' meta
  tmp <- newNameWith "tmp"
  insTypeEnv tmp t
  asms <- asmData tmp d
  return $ asms ++ [AsmReturn tmp]
asmCode (CodeLet i d@(meta :< _) cont) = do
  t <- lookupTypeEnv' meta
  loader <- newNameWith "loader"
  insTypeEnv loader t
  bindLoader <- asmData loader d
  cont' <- asmCode cont
  return $ bindLoader ++ asmCopy t (AsmDataRegister loader) i ++ cont'
asmCode (CodeSwitch basePointer defaultBranch branchList) = do
  tagPtr <- newNameWith $ basePointer ++ ".tagptr"
  insTypeEnv tagPtr $ Fix $ TypeInt 32
  headData <- newNameWith $ basePointer ++ ".kind"
  insTypeEnv headData $ Fix $ TypeInt 32
  branchList' <-
    forM branchList $ \(name, ident, label, code) -> do
      asm <- asmCode code
      return (name, ident, label, asm)
  return
    [ AsmLet tagPtr (AsmGetElemPointer basePointer [0, 0])
    , AsmLet headData (AsmLoad tagPtr)
    , AsmSwitch headData defaultBranch branchList'
    ]
asmCode (CodeCall x name args cont) = do
  varAsmList <-
    forM args $ \arg@(meta :< _) -> do
      tmp <- newNameWith "tmp"
      t <- lookupTypeEnv' meta
      insTypeEnv tmp t
      asm <- asmData tmp arg
      return (tmp, asm)
  let (varList, asmList) = unzip varAsmList
  asmCont <- asmCode cont
  return $ join asmList ++ [AsmLet x (AsmCall name varList)] ++ asmCont
asmCode (CodeCallClosure x cls@(clsMeta :< _) cont) = do
  clsType <- lookupTypeEnv' clsMeta
  clsReg <- newNameWith "cls"
  funPtr <- newNameWith $ "cls" ++ ".cursor00"
  insTypeEnv funPtr clsType
  envPtr <- newNameWith $ "cls" ++ ".cursor010"
  insTypeEnv envPtr $ Fix $ TypeDown $ Fix TypeOpaque
  bindClsReg <- asmData clsReg cls
  asmCont <- asmCode cont
  return $
    bindClsReg ++
    [ AsmLet funPtr (AsmGetElemPointer clsReg [0, 0])
    , AsmLet envPtr (AsmGetElemPointer clsReg [0, 1, 0]) -- opaque pointer?
    , AsmLet x (AsmCall funPtr [envPtr])
    ] ++
    asmCont

asmData :: Identifier -> Data -> WithEnv [Asm]
asmData tmp (_ :< DataPointer x) = do
  t <- lookupTypeEnv' x
  return $ asmCopy t (AsmDataRegister x) tmp
asmData tmp (_ :< DataFunName name) = do
  let labelPointerType = Fix $ TypeDown $ Fix $ TypeInt 8
  return $ asmCopy labelPointerType (AsmDataLabel name) tmp
asmData tmp (_ :< DataElemAtIndex basePointer idx) =
  return [AsmLet tmp (AsmGetElemPointer basePointer idx)]
asmData tmp (meta :< DataInt32 i) = do
  baseType <- lookupTypeEnv' meta -- i32*
  return $ asmCopy baseType (AsmDataInt i) tmp
  return [AsmLet tmp (AsmAlloc baseType), AsmStore baseType (AsmDataInt i) tmp]
asmData tmp (_ :< DataClosure name fvListPtr fvList) = do
  varAsmList <-
    forM fvList $ \fv -> do
      var <- newNameWith "tmp"
      t <- lookupTypeEnv' fv
      insTypeEnv var t
      return (var, asmCopy t (AsmDataRegister fv) var)
  let (varList, copyFreeVar) = unzip varAsmList
  typeList <- mapM lookupTypeEnv' varList
  let varList' = map AsmDataRegister varList
  let structType = Fix (TypeStruct typeList)
  let labelType = Fix (TypeDown (Fix (TypeInt 32)))
  let clsType = Fix (TypeStruct [labelType, Fix (TypeDown structType)])
  let cls = AsmDataStruct [AsmDataLabel name, AsmDataRegister fvListPtr]
  return $
    join copyFreeVar ++
    asmCopy structType (AsmDataStruct varList') fvListPtr ++
    asmCopy clsType cls tmp

asmCopy :: Type -> AsmData -> Identifier -> [Asm]
asmCopy t from to = [AsmLet to (AsmAlloc t), AsmStore t from to]
