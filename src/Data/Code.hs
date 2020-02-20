module Data.Code where

import Data.Maybe (fromMaybe)
import Numeric.Half

import Data.Basic

-- The definition of `Data` doesn't contain those type-level definitions like `DataTau`
-- since they are translated to "exponents" immediately after polarization (and thus in Clarify.hs).
data Data
  = DataTheta Identifier
  | DataUpsilon Identifier
  | DataSigmaIntro ArrayKind [DataPlus]
  | DataFloat16 Half
  | DataFloat32 Float
  | DataFloat64 Double
  | DataEnumIntro EnumValue
  | DataStructIntro [(DataPlus, ArrayKind)]
  deriving (Show)

data Code
  = CodeTheta Theta
  | CodePiElimDownElim DataPlus [DataPlus] -- ((force v) v1 ... vn)
  -- the variable introduced by CodeSigmaElim is must be used (practically) linearly
  | CodeSigmaElim
      ArrayKind
      [(Identifier, CodePlus)] -- [(x1, return t1), ..., (xn, return tn)] with xi : ti
      DataPlus
      CodePlus
  | CodeUpIntro DataPlus
  -- the variable introduced by CodeUpElim is assumed to be used linearly
  -- (this property is exploited to, for example, prevent unnecessary copy of array in array-access)
  | CodeUpElim Identifier CodePlus CodePlus
  | CodeEnumElim SubstDataPlus DataPlus [(Case, CodePlus)]
  | CodeStructElim [(Identifier, ArrayKind)] DataPlus CodePlus
  deriving (Show)

data Theta
  = ThetaUnaryOp UnaryOp LowType DataPlus
  | ThetaBinaryOp BinaryOp LowType DataPlus DataPlus
  | ThetaArrayAccess LowType DataPlus DataPlus
  | ThetaSysCall SysCall [DataPlus]
  deriving (Show)

type IdentifierPlus = (Identifier, DataPlus)

type DataPlus = (Meta, Data)

type CodePlus = (Meta, Code)

toDataUpsilon :: (Identifier, Meta) -> DataPlus
toDataUpsilon (x, m) = (m, DataUpsilon x)

toDataUpsilon' :: Identifier -> DataPlus
toDataUpsilon' x = (emptyMeta, DataUpsilon x)

toIntS :: IntSize -> Int -> Data
toIntS size i = DataEnumIntro (EnumValueIntS size i)

toIntU :: IntSize -> Int -> Data
toIntU size i = DataEnumIntro (EnumValueIntU size i)

type SubstDataPlus = [(Identifier, DataPlus)]

substDataPlus :: SubstDataPlus -> DataPlus -> DataPlus
substDataPlus _ (m, DataTheta x) = (m, DataTheta x)
substDataPlus sub (m, DataUpsilon s) =
  fromMaybe (m, DataUpsilon s) (lookup s sub)
substDataPlus sub (m, DataSigmaIntro mk vs) = do
  let vs' = map (substDataPlus sub) vs
  (m, DataSigmaIntro mk vs')
substDataPlus _ (m, DataFloat16 l) = (m, DataFloat16 l)
substDataPlus _ (m, DataFloat32 l) = (m, DataFloat32 l)
substDataPlus _ (m, DataFloat64 l) = (m, DataFloat64 l)
substDataPlus _ (m, DataEnumIntro l) = (m, DataEnumIntro l)
substDataPlus sub (m, DataStructIntro dks) = do
  let (ds, ks) = unzip dks
  let ds' = map (substDataPlus sub) ds
  (m, DataStructIntro $ zip ds' ks)

substCodePlus :: SubstDataPlus -> CodePlus -> CodePlus
substCodePlus sub (m, CodeTheta theta) = do
  let theta' = substTheta sub theta
  (m, CodeTheta theta')
substCodePlus sub (m, CodePiElimDownElim v ds) = do
  let v' = substDataPlus sub v
  let ds' = map (substDataPlus sub) ds
  (m, CodePiElimDownElim v' ds')
substCodePlus sub (m, CodeSigmaElim mk xts v e) = do
  let v' = substDataPlus sub v
  let (xts', e') = substDataPlusSigmaElim sub xts e
  (m, CodeSigmaElim mk xts' v' e')
substCodePlus sub (m, CodeUpIntro v) = do
  let v' = substDataPlus sub v
  (m, CodeUpIntro v')
substCodePlus sub (m, CodeUpElim x e1 e2) = do
  let e1' = substCodePlus sub e1
  let sub' = filter (\(y, _) -> y /= x) sub
  let e2' = substCodePlus sub' e2
  (m, CodeUpElim x e1' e2')
substCodePlus sub (m, CodeEnumElim fvInfo v branchList) = do
  let (from, to) = unzip fvInfo
  let to' = map (substDataPlus sub) to
  let fvInfo' = zip from to'
  let v' = substDataPlus sub v
  (m, CodeEnumElim fvInfo' v' branchList)
substCodePlus sub (m, CodeStructElim xks v e) = do
  let v' = substDataPlus sub v
  let sub' = filter (\(k, _) -> k `notElem` map fst xks) sub
  let e' = substCodePlus sub' e
  (m, CodeStructElim xks v' e')

substTheta :: SubstDataPlus -> Theta -> Theta
substTheta sub (ThetaUnaryOp a t v) = do
  let v' = substDataPlus sub v
  ThetaUnaryOp a t v'
substTheta sub (ThetaBinaryOp a t v1 v2) = do
  let v1' = substDataPlus sub v1
  let v2' = substDataPlus sub v2
  ThetaBinaryOp a t v1' v2'
substTheta sub (ThetaArrayAccess t d1 d2) = do
  let d1' = substDataPlus sub d1
  let d2' = substDataPlus sub d2
  ThetaArrayAccess t d1' d2'
substTheta sub (ThetaSysCall sysCall ds) = do
  let ds' = map (substDataPlus sub) ds
  ThetaSysCall sysCall ds'

substDataPlusSigmaElim ::
     SubstDataPlus
  -> [(Identifier, CodePlus)]
  -> CodePlus
  -> ([(Identifier, CodePlus)], CodePlus)
substDataPlusSigmaElim sub [] e = ([], substCodePlus sub e)
substDataPlusSigmaElim sub ((x, t):xs) e = do
  let t' = substCodePlus sub t
  let sub' = filter (\(y, _) -> y /= x) sub
  let (xs', e') = substDataPlusSigmaElim sub' xs e
  ((x, t') : xs', e')
