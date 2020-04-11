module Data.Code where

import Data.Maybe (fromMaybe)

import qualified Data.IntMap.Strict as IntMap
import qualified Data.Text as T

import Data.Basic

data Data
  = DataConst T.Text
  | DataUpsilon Identifier
  | DataSigmaIntro ArrayKind [DataPlus]
  | DataEnumIntro EnumValue
  | DataFloat FloatSize Double
  | DataStructIntro [(DataPlus, ArrayKind)]
  deriving (Show)

data Code
  = CodeConst Const
  | CodePiElimDownElim DataPlus [DataPlus] -- ((force v) v1 ... vn)
  | CodeSigmaElim ArrayKind [Identifier] DataPlus CodePlus
  | CodeUpIntro DataPlus
  | CodeUpElim Identifier CodePlus CodePlus
  | CodeEnumElim SubstDataPlus DataPlus [(Case, CodePlus)]
  | CodeStructElim [(Identifier, ArrayKind)] DataPlus CodePlus
  | CodeCase SubstDataPlus DataPlus [((Meta, T.Text), CodePlus)]
  deriving (Show)

data Const
  = ConstUnaryOp UnaryOp DataPlus
  | ConstBinaryOp BinaryOp DataPlus DataPlus
  | ConstArrayAccess LowType DataPlus DataPlus
  | ConstSysCall Syscall [DataPlus]
  deriving (Show)

newtype IsFixed =
  IsFixed Bool
  deriving (Show)

data Definition =
  Definition IsFixed [Identifier] CodePlus
  deriving (Show)

type DataPlus = (Meta, Data)

type CodePlus = (Meta, Code)

asUpsilon :: DataPlus -> Maybe Identifier
asUpsilon (_, DataUpsilon x) = Just x
asUpsilon _ = Nothing

sigmaIntro :: [DataPlus] -> Data
sigmaIntro = DataSigmaIntro arrVoidPtr

sigmaElim :: [Identifier] -> DataPlus -> CodePlus -> Code
sigmaElim = CodeSigmaElim arrVoidPtr

type SubstDataPlus = IntMap.IntMap DataPlus

substDataPlus :: SubstDataPlus -> DataPlus -> DataPlus
substDataPlus _ (m, DataConst x) = (m, DataConst x)
substDataPlus sub (m, DataUpsilon s) =
  fromMaybe (m, DataUpsilon s) (IntMap.lookup (asInt s) sub) -- ここではsの整数部分を比較したほうがよさそう？
substDataPlus sub (m, DataSigmaIntro mk vs) = do
  let vs' = map (substDataPlus sub) vs
  (m, DataSigmaIntro mk vs')
substDataPlus _ (m, DataFloat size l) = (m, DataFloat size l)
substDataPlus _ (m, DataEnumIntro l) = (m, DataEnumIntro l)
substDataPlus sub (m, DataStructIntro dks) = do
  let (ds, ks) = unzip dks
  let ds' = map (substDataPlus sub) ds
  (m, DataStructIntro $ zip ds' ks)

substCodePlus :: SubstDataPlus -> CodePlus -> CodePlus
substCodePlus sub (m, CodeConst theta) = do
  let theta' = substConst sub theta
  (m, CodeConst theta')
substCodePlus sub (m, CodePiElimDownElim v ds) = do
  let v' = substDataPlus sub v
  let ds' = map (substDataPlus sub) ds
  (m, CodePiElimDownElim v' ds')
substCodePlus sub (m, CodeSigmaElim mk xs v e) = do
  let v' = substDataPlus sub v
  let sub' = deleteKeys sub (map asInt xs)
  let e' = substCodePlus sub' e
  (m, CodeSigmaElim mk xs v' e')
substCodePlus sub (m, CodeUpIntro v) = do
  let v' = substDataPlus sub v
  (m, CodeUpIntro v')
substCodePlus sub (m, CodeUpElim x e1 e2) = do
  let e1' = substCodePlus sub e1
  let sub' = IntMap.delete (asInt x) sub
  let e2' = substCodePlus sub' e2
  (m, CodeUpElim x e1' e2')
substCodePlus sub (m, CodeEnumElim fvInfo v branchList) = do
  let fvInfo' = IntMap.map (substDataPlus sub) fvInfo
  let v' = substDataPlus sub v
  (m, CodeEnumElim fvInfo' v' branchList)
substCodePlus sub (m, CodeStructElim xks v e) = do
  let v' = substDataPlus sub v
  let sub' = deleteKeys sub (map (asInt . fst) xks)
  let e' = substCodePlus sub' e
  (m, CodeStructElim xks v' e')
substCodePlus sub (m, CodeCase fvInfo v branchList) = do
  let fvInfo' = IntMap.map (substDataPlus sub) fvInfo
  let v' = substDataPlus sub v
  (m, CodeCase fvInfo' v' branchList)

substConst :: SubstDataPlus -> Const -> Const
substConst sub (ConstUnaryOp a v) = do
  let v' = substDataPlus sub v
  ConstUnaryOp a v'
substConst sub (ConstBinaryOp a v1 v2) = do
  let v1' = substDataPlus sub v1
  let v2' = substDataPlus sub v2
  ConstBinaryOp a v1' v2'
substConst sub (ConstArrayAccess t d1 d2) = do
  let d1' = substDataPlus sub d1
  let d2' = substDataPlus sub d2
  ConstArrayAccess t d1' d2'
substConst sub (ConstSysCall sysCall ds) = do
  let ds' = map (substDataPlus sub) ds
  ConstSysCall sysCall ds'
