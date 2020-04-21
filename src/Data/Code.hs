module Data.Code where

import Data.Basic
import qualified Data.IntMap as IntMap
import Data.Maybe (fromMaybe)
import qualified Data.Text as T

data Data
  = DataConst T.Text
  | DataUpsilon Ident
  | DataSigmaIntro ArrayKind [DataPlus]
  | DataEnumIntro EnumValue
  | DataFloat FloatSize Double
  | DataStructIntro [(DataPlus, ArrayKind)]
  deriving (Show)

data Code
  = CodeConst Const
  | CodePiElimDownElim DataPlus [DataPlus] -- ((force v) v1 ... vn)
  | CodeSigmaElim ArrayKind [Ident] DataPlus CodePlus
  | CodeUpIntro DataPlus
  | CodeUpElim Ident CodePlus CodePlus
  | CodeEnumElim SubstDataPlus DataPlus [(Case, CodePlus)]
  | CodeStructElim [(Ident, ArrayKind)] DataPlus CodePlus
  | CodeCase SubstDataPlus DataPlus [((Meta, T.Text), CodePlus)]
  deriving (Show)

data Const
  = ConstUnaryOp UnaryOp DataPlus
  | ConstBinaryOp BinaryOp DataPlus DataPlus
  | ConstArrayAccess LowType DataPlus DataPlus
  | ConstSysCall Syscall [DataPlus]
  deriving (Show)

newtype IsFixed
  = IsFixed Bool
  deriving (Show)

data Definition
  = Definition IsFixed [Ident] CodePlus
  deriving (Show)

type DataPlus = (Meta, Data)

type CodePlus = (Meta, Code)

asUpsilon :: DataPlus -> Maybe Ident
asUpsilon term =
  case term of
    (_, DataUpsilon x) ->
      Just x
    _ ->
      Nothing

sigmaIntro :: [DataPlus] -> Data
sigmaIntro = DataSigmaIntro arrVoidPtr

sigmaElim :: [Ident] -> DataPlus -> CodePlus -> Code
sigmaElim = CodeSigmaElim arrVoidPtr

type SubstDataPlus = IntMap.IntMap DataPlus

substDataPlus :: SubstDataPlus -> DataPlus -> DataPlus
substDataPlus sub term =
  case term of
    (m, DataConst x) ->
      (m, DataConst x)
    (m, DataUpsilon s) ->
      fromMaybe (m, DataUpsilon s) (IntMap.lookup (asInt s) sub) -- ここではsの整数部分を比較したほうがよさそう？
    (m, DataSigmaIntro mk vs) -> do
      let vs' = map (substDataPlus sub) vs
      (m, DataSigmaIntro mk vs')
    (m, DataFloat size l) ->
      (m, DataFloat size l)
    (m, DataEnumIntro l) ->
      (m, DataEnumIntro l)
    (m, DataStructIntro dks) -> do
      let (ds, ks) = unzip dks
      let ds' = map (substDataPlus sub) ds
      (m, DataStructIntro $ zip ds' ks)

substCodePlus :: SubstDataPlus -> CodePlus -> CodePlus
substCodePlus sub term =
  case term of
    (m, CodeConst theta) -> do
      let theta' = substConst sub theta
      (m, CodeConst theta')
    (m, CodePiElimDownElim v ds) -> do
      let v' = substDataPlus sub v
      let ds' = map (substDataPlus sub) ds
      (m, CodePiElimDownElim v' ds')
    (m, CodeSigmaElim mk xs v e) -> do
      let v' = substDataPlus sub v
      let sub' = deleteKeys sub (map asInt xs)
      let e' = substCodePlus sub' e
      (m, CodeSigmaElim mk xs v' e')
    (m, CodeUpIntro v) -> do
      let v' = substDataPlus sub v
      (m, CodeUpIntro v')
    (m, CodeUpElim x e1 e2) -> do
      let e1' = substCodePlus sub e1
      let sub' = IntMap.delete (asInt x) sub
      let e2' = substCodePlus sub' e2
      (m, CodeUpElim x e1' e2')
    (m, CodeEnumElim fvInfo v branchList) -> do
      let fvInfo' = IntMap.map (substDataPlus sub) fvInfo
      let v' = substDataPlus sub v
      (m, CodeEnumElim fvInfo' v' branchList)
    (m, CodeStructElim xks v e) -> do
      let v' = substDataPlus sub v
      let sub' = deleteKeys sub (map (asInt . fst) xks)
      let e' = substCodePlus sub' e
      (m, CodeStructElim xks v' e')
    (m, CodeCase fvInfo v branchList) -> do
      let fvInfo' = IntMap.map (substDataPlus sub) fvInfo
      let v' = substDataPlus sub v
      (m, CodeCase fvInfo' v' branchList)

substConst :: SubstDataPlus -> Const -> Const
substConst sub c =
  case c of
    ConstUnaryOp a v -> do
      let v' = substDataPlus sub v
      ConstUnaryOp a v'
    ConstBinaryOp a v1 v2 -> do
      let v1' = substDataPlus sub v1
      let v2' = substDataPlus sub v2
      ConstBinaryOp a v1' v2'
    ConstArrayAccess t d1 d2 -> do
      let d1' = substDataPlus sub d1
      let d2' = substDataPlus sub d2
      ConstArrayAccess t d1' d2'
    ConstSysCall sysCall ds -> do
      let ds' = map (substDataPlus sub) ds
      ConstSysCall sysCall ds'
