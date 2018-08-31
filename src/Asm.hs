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
  copy <- asmCopy (AsmDataRegister loader) i
  return $ bindLoader ++ copy ++ cont'
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
asmCode (CodeCall x fun args cont) = do
  (varList, asmList) <- toVarAsmList args
  asmCont <- asmCode cont
  return $ join asmList ++ [AsmLet x (AsmCall fun varList)] ++ asmCont
-- asmCode (CodeCallCls x cls args cont) = do
--   (varList, asmList) <- toVarAsmList args
--   asmCont <- asmCode cont
--   funPtr <- newNameWith "cls.0"
--   insTypeEnv funPtr $ Fix $ TypeDown $ Fix $ TypeInt 32
--   envPtr <- newNameWith "env"
--   headData <- newNameWith $ "cls" ++ "0"
--   insTypeEnv headData $ Fix $ TypeInt 32
--   clsVar <- newNameWith "cls"
--   bindCls <- asmData clsVar cls
--     -- Fix $ TypeDown $ Fix $ TypeStruct [labelType, envType]
--   return $
--     join asmList ++
--     bindCls ++
--     [ AsmLet funPtr (AsmGetElemPointer clsVar [0, 0])
--     , AsmLet envPtr (AsmGetElemPointer clsVar [0, 1])
--     ] ++
--     [AsmLet x (AsmCall funPtr (envPtr : varList))] ++ asmCont
-- asmCode (CodeLoadClosure cls@(clsMeta :< _)) = do
--   clsPtrType <- lookupTypeEnv' clsMeta
--   clsPtrReg <- newNameWith "cls"
--   insTypeEnv clsPtrReg clsPtrType
--   asmData clsPtrReg cls
asmCode (CodeLoad d@(meta :< _)) = do
  t <- lookupTypeEnv' meta
  x <- newNameWith "tmp"
  insTypeEnv x t
  tmp <- newNameWith "tmp"
  insTypeEnv tmp t
  bindDataToVar <- asmData tmp d
  return $ bindDataToVar ++ [AsmLet x (AsmLoad tmp), AsmReturn x]

toVarAsmList :: [Data] -> WithEnv ([Identifier], [[Asm]])
toVarAsmList args = do
  varAsmList <-
    forM args $ \arg@(meta :< _) -> do
      tmp <- newNameWith "tmp"
      t <- lookupTypeEnv' meta
      insTypeEnv tmp t
      asm <- asmData tmp arg
      return (tmp, asm)
  return $ unzip varAsmList

asmData :: Identifier -> Data -> WithEnv [Asm]
asmData tmp (_ :< DataRegister x) = asmCopy (AsmDataRegister x) tmp
asmData tmp (_ :< DataPointer x) = asmCopy (AsmDataRegister x) tmp
-- asmData tmp (_ :< DataFunName name) = asmCopy (AsmDataFunName name) tmp
asmData tmp (_ :< DataElemAtIndex basePointer idx) =
  return [AsmLet tmp (AsmGetElemPointer basePointer idx)]
asmData tmp (_ :< DataInt32 i) = asmCopy (AsmDataInt32 i) tmp

-- asmData tmp (_ :< DataClosure name fvListPtr fvList) = do
--   typeList <- mapM lookupTypeEnv' fvList
--   let contentList = zip (map AsmDataRegister fvList) typeList
--   setFvListPtrContent <- setContent contentList fvListPtr
--   let structType = Fix (TypeStruct typeList)
--   let labelType = Fix (TypeDown (Fix (TypeInt 8)))
--   let fvListPtrType = Fix $ TypeDown structType
--   let clsType = Fix (TypeStruct [labelType, fvListPtrType])
--   let clsContentList =
--         [ (AsmDataFunName name, labelType)
--         , (AsmDataRegister fvListPtr, fvListPtrType)
--         ]
--   setClsContent <- setContent clsContentList tmp
--   insLowTypeEnv tmp $ Fix $ TypeDown clsType
--   return $
--     [AsmLet fvListPtr (AsmAlloc structType)] ++
--     setFvListPtrContent ++ [AsmLet tmp (AsmAlloc clsType)] ++ setClsContent
-- temporary
asmCopy :: AsmData -> Identifier -> WithEnv [Asm]
asmCopy from to = do
  t <- lookupTypeEnv' to
  t' <- unwrapDown t
  -- undefined
  -- tmp <- newNameWith "copy"
  -- insTypeEnv tmp t'
  return [AsmLet to (AsmAlloc t'), AsmStore from to]

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
