module Data.Code where

import Data.Maybe (fromMaybe)
import Numeric.Half

import Data.Basic

-- The definition of `Data` doesn't contain those type-level definitions like `DataTau`
-- since they are translated to "exponents" immediately after polarization (and thus in Clarify.hs).
data Data
  = DataTheta Identifier
  | DataUpsilon Identifier
  | DataSigmaIntro [DataPlus]
  | DataIntS IntSize Integer
  | DataIntU IntSize Integer
  | DataFloat16 Half
  | DataFloat32 Float
  | DataFloat64 Double
  | DataEnumIntro EnumValue
  | DataArrayIntro ArrayKind [(EnumValue, DataPlus)]
  deriving (Show)

data Code
  = CodeTheta Theta
  | CodePiElimDownElim DataPlus [DataPlus] -- ((force v) v1 ... vn)
  | CodeSigmaElim
      (Maybe ArrayKind)
      [(Identifier, CodePlus)] -- [(x1, return t1), ..., (xn, return tn)] with xi : ti
      DataPlus
      CodePlus
  | CodeUpIntro DataPlus
  | CodeUpElim Identifier CodePlus CodePlus
  | CodeEnumElim DataPlus [(Case, CodePlus)]
  | CodeArrayElim ArrayKind DataPlus DataPlus
  deriving (Show)

data Theta
  = ThetaUnaryOp UnaryOp LowType DataPlus
  | ThetaBinaryOp BinaryOp LowType DataPlus DataPlus
  | ThetaSysCall SysCall [DataPlus]
  deriving (Show)

type IdentifierPlus = (Identifier, DataPlus)

type DataPlus = (Meta, Data)

type CodePlus = (Meta, Code)

toDataUpsilon :: (Identifier, Meta) -> DataPlus
toDataUpsilon (x, m) = (m, DataUpsilon x)

toDataUpsilon' :: Identifier -> DataPlus
toDataUpsilon' x = (emptyMeta, DataUpsilon x)

type SubstDataPlus = [(Identifier, DataPlus)]

substDataPlus :: SubstDataPlus -> DataPlus -> DataPlus
substDataPlus _ (m, DataTheta x) = (m, DataTheta x)
substDataPlus sub (m, DataUpsilon s) =
  fromMaybe (m, DataUpsilon s) (lookup s sub)
substDataPlus sub (m, DataSigmaIntro vs) = do
  let vs' = map (substDataPlus sub) vs
  (m, DataSigmaIntro vs')
substDataPlus _ (m, DataIntS size l) = (m, DataIntS size l)
substDataPlus _ (m, DataIntU size l) = (m, DataIntU size l)
substDataPlus _ (m, DataFloat16 l) = (m, DataFloat16 l)
substDataPlus _ (m, DataFloat32 l) = (m, DataFloat32 l)
substDataPlus _ (m, DataFloat64 l) = (m, DataFloat64 l)
substDataPlus _ (m, DataEnumIntro l) = (m, DataEnumIntro l)
substDataPlus sub (m, DataArrayIntro k lds) = do
  let (ls, ds) = unzip lds
  let ds' = map (substDataPlus sub) ds
  (m, DataArrayIntro k $ zip ls ds')

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
substCodePlus sub (m, CodeEnumElim v branchList) = do
  let v' = substDataPlus sub v
  let (cs, es) = unzip branchList
  let es' = map (substCodePlus sub) es
  let branchList' = zip cs es'
  (m, CodeEnumElim v' branchList')
substCodePlus sub (m, CodeArrayElim k d1 d2) = do
  let d1' = substDataPlus sub d1
  let d2' = substDataPlus sub d2
  (m, CodeArrayElim k d1' d2')

substTheta :: SubstDataPlus -> Theta -> Theta
substTheta sub (ThetaUnaryOp a t v) = do
  let v' = substDataPlus sub v
  ThetaUnaryOp a t v'
substTheta sub (ThetaBinaryOp a t v1 v2) = do
  let v1' = substDataPlus sub v1
  let v2' = substDataPlus sub v2
  ThetaBinaryOp a t v1' v2'
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

varData :: DataPlus -> [Identifier]
varData (_, DataUpsilon x) = [x]
varData (_, DataSigmaIntro ds) = concatMap varData ds
varData (_, DataArrayIntro _ lds) = concatMap (varData . snd) lds
varData _ = []

varCode :: CodePlus -> [Identifier]
varCode (_, CodeTheta theta) = varTheta theta
varCode (_, CodePiElimDownElim d ds) = concatMap varData $ d : ds
varCode (_, CodeSigmaElim _ xts d e) = varData d ++ varCode' xts e
varCode (_, CodeUpIntro d) = varData d
varCode (_, CodeUpElim x e1 e2) = varCode e1 ++ filter (/= x) (varCode e2)
varCode (_, CodeEnumElim d les) = do
  let (_, es) = unzip les
  varData d ++ concatMap varCode es
varCode (_, CodeArrayElim _ d1 d2) = varData d1 ++ varData d2

varTheta :: Theta -> [Identifier]
varTheta (ThetaUnaryOp _ _ d) = varData d
varTheta (ThetaBinaryOp _ _ d1 d2) = varData d1 ++ varData d2
varTheta (ThetaSysCall _ ds) = concatMap varData ds

varCode' :: [(Identifier, CodePlus)] -> CodePlus -> [Identifier]
varCode' [] e = varCode e
varCode' ((x, t):xts) e = varCode t ++ (filter ((/=) x) $ varCode' xts e)
