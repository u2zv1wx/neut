module Asm
  ( asmCode
  , asmConstructor
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
asmCode (CodeSwitch basePointer (defaultLabel, defaultCode) branchList) = do
  tagPtr <- newNameWith $ basePointer ++ ".tagptr"
  insTypeEnv tagPtr $ Fix $ TypeDown $ Fix $ TypeInt 32
  headData <- newNameWith $ basePointer ++ ".kind"
  insTypeEnv headData $ Fix $ TypeInt 32
  defaultAsm <- asmCode defaultCode
  branchList' <-
    forM branchList $ \(name, ident, label, code) -> do
      asm <- asmCode code
      return (name, ident, label, asm)
  return
    [ AsmLet tagPtr (AsmGetElemPointer basePointer [0, 0])
    , AsmLet headData (AsmLoad tagPtr)
    , AsmSwitch headData (defaultLabel, defaultAsm) branchList'
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
  insTypeEnv clsReg $ Fix $ TypeDown $ Fix $ TypeStruct []
  funPtr <- newNameWith $ "cls" ++ ".cursor00"
  insTypeEnv funPtr clsType
  envPtr <- newNameWith $ "cls" ++ ".cursor010"
  insTypeEnv envPtr $ Fix $ TypeDown $ Fix TypeOpaque
  bindClsReg <- asmData clsReg cls
  asmCont <- asmCode cont
  return $
    bindClsReg ++
    [ AsmLet funPtr (AsmGetElemPointer clsReg [0, 0])
    , AsmLet envPtr (AsmGetElemPointer clsReg [0, 1, 0])
    , AsmLet x (AsmCall funPtr [envPtr])
    ] ++
    asmCont

asmData :: Identifier -> Data -> WithEnv [Asm]
asmData tmp (_ :< DataPointer x) = do
  t <- lookupTypeEnv' x
  return $ asmCopy t (AsmDataRegister x) tmp
asmData tmp (_ :< DataFunName name) = do
  let labelPointerType = Fix $ TypeDown $ Fix $ TypeInt 8
  return $ asmCopy labelPointerType (AsmDataFunName name) tmp
asmData tmp (_ :< DataElemAtIndex basePointer idx) =
  return [AsmLet tmp (AsmGetElemPointer basePointer idx)]
asmData tmp (meta :< DataInt32 i) = do
  baseType <- lookupTypeEnv' meta -- i32*
  return $ asmCopy baseType (AsmDataInt32 i) tmp
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
  let contentList = zip varList' typeList
  let structType = Fix (TypeStruct typeList)
  let labelType = Fix (TypeDown (Fix (TypeInt 8)))
  let clsType = Fix (TypeStruct [labelType, Fix (TypeDown structType)])
  setEnvContent <- setContent contentList fvListPtr
  let clsContentList =
        [(AsmDataFunName name, labelType), (AsmDataRegister fvListPtr, clsType)]
  setClsContent <- setContent clsContentList tmp
  return $
    join copyFreeVar ++
    [AsmLet fvListPtr (AsmAlloc structType)] ++
    setEnvContent ++ [AsmLet tmp (AsmAlloc clsType)] ++ setClsContent

asmCopy :: Type -> AsmData -> Identifier -> [Asm]
asmCopy t from to = [AsmLet to (AsmAlloc t), AsmStore from to]

asmConstructor :: Identifier -> Type -> WithEnv [Asm]
asmConstructor name t = do
  let (_, identArgTypes) = forallArgs t
  let (identList, argTypes) = unzip identArgTypes
  let regList = map AsmDataRegister identList
  let num = 1 :: Int
  let contentList = (AsmDataInt32 num, Fix (TypeInt 32)) : zip regList argTypes
  let resultType = Fix $ TypeStruct $ Fix (TypeInt 32) : argTypes
  let constructorCodType = Fix $ TypeDown resultType
  let t' = Fix $ TypeDown $ coForallArgs (constructorCodType, identArgTypes)
  insTypeEnv name t'
  resultPtr <- newNameWith "tmp"
  insTypeEnv resultPtr constructorCodType
  setStructContent <- setContent contentList resultPtr
  result <- newNameWith "result"
  insTypeEnv result resultType
  return $
    [AsmLet resultPtr (AsmAlloc resultType)] ++
    setStructContent ++
    [AsmLet result (AsmLoad resultPtr)] ++ [AsmReturn result]
    --[AsmReturn resultPtr]

setContent :: [(AsmData, Type)] -> Identifier -> WithEnv [Asm]
setContent contentList basePointer = do
  asmListList <-
    forM (zip contentList [0 ..]) $ \((asmData, t), index) -> do
      cursor <- newNameWith $ "cursor" ++ show index
      insTypeEnv cursor $ Fix $ TypeDown t
      return
        [ AsmLet cursor (AsmGetElemPointer basePointer [0, index])
        , AsmStore asmData cursor
        ]
  return $ join asmListList
