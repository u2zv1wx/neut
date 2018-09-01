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
  copy <- asmCopy (AsmDataLocal loader) i
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
asmCode (CodeLoad d@(meta :< _))
  -- call d
 = do
  t <- lookupTypeEnv' meta
  x <- newNameWith "tmp"
  insTypeEnv x t
  tmp <- newNameWith "tmp"
  insTypeEnv tmp t
  bindDataToVar <- asmData tmp d
  return $ bindDataToVar ++ [AsmLet x (AsmCall tmp []), AsmReturn x]

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
asmData tmp (_ :< DataLocal x) = asmCopy (AsmDataLocal x) tmp
asmData tmp (_ :< DataGlobal x) = asmCopy (AsmDataGlobal x) tmp
asmData tmp (_ :< DataElemAtIndex basePointer idx) =
  return [AsmLet tmp (AsmGetElemPointer basePointer idx)]
asmData tmp (_ :< DataInt32 i) = asmCopy (AsmDataInt32 i) tmp

-- temporary
asmCopy :: AsmData -> Identifier -> WithEnv [Asm]
asmCopy from to = do
  t <- lookupTypeEnv' to
  t' <- unwrapDown t
  return [AsmLet to (AsmAlloc t'), AsmStore from to]

asmConstructor :: Identifier -> Type -> WithEnv [Asm]
asmConstructor name t = do
  let (_, identArgTypes) = forallArgs t
  let (identList, argTypes) = unzip identArgTypes
  let regList = map AsmDataLocal identList
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
