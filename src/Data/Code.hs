module Data.Code where

import Data.Basic
import Data.Maybe (fromMaybe)

-- The definition of `Data` doesn't contain those type-level definitions like `DataTau`
-- since they are translated to "exponents" immediately after polarization (and thus in Polarize.hs).
data Data
  = DataTheta Identifier -- global variable
  | DataUpsilon Identifier
  | DataEpsilonIntro Literal LowType
  | DataDownIntroPiIntro [Identifier] CodePlus
  | DataSigmaIntro [DataPlus]
  deriving (Show)

data Code
  = CodeTheta Theta
  | CodeEpsilonElim Identifier DataPlus [(Case, CodePlus)]
  -- In contrast with CBPV, the arguments are negative since they are supposed to be of type ↑P.
  -- This modification is essential when we consider a dependent variant of CBPV translation.
  -- Or more concretely: Since we don't have the distinction between terms and types anymore, the `A` in
  -- `Pi (x : A). B` must be translated using the same function for terms. Thus, the `A` is
  -- translated into a negative term `return v`, where `v` is some positive term which is supposed to be
  -- beta-equivalent to a positive type. To extract this `v` part without resorting
  -- pattern-matching in compiler, we need some tricks here. And the trick is: set the type of
  -- domain of Pi-types to be negative, and translate that `A` into `bind z := A^# in ↑z`.
  -- This is why the domain of Pi-type must be negative in dependent CBPV.
  | CodePiElimDownElim DataPlus [CodePlus] -- ((force v) e1 ... en)
  | CodeSigmaElim [Identifier] DataPlus CodePlus
  | CodeUpIntro DataPlus
  | CodeCopyN DataPlus DataPlus
  | CodeTransposeN DataPlus [DataPlus]
  deriving (Show)

data Theta
  = ThetaArith Arith LowType DataPlus DataPlus
  | ThetaPrint DataPlus
  deriving (Show)

type IdentifierPlus = (Identifier, DataPlus)

type CodeMeta = Maybe Loc

type DataPlus = (CodeMeta, Data)

type CodePlus = (CodeMeta, Code)

toDataUpsilon :: (Identifier, Maybe Loc) -> DataPlus
toDataUpsilon (x, ml) = (ml, DataUpsilon x)

toDataUpsilon' :: Identifier -> DataPlus
toDataUpsilon' x = (Nothing, DataUpsilon x)

varDataPlus :: DataPlus -> [Identifier]
varDataPlus (_, DataTheta _) = []
varDataPlus (_, DataUpsilon x) = [x]
varDataPlus (_, DataEpsilonIntro _ _) = []
varDataPlus (_, DataDownIntroPiIntro xs e) =
  filter (`notElem` xs) $ varCodePlus e
varDataPlus (_, DataSigmaIntro vs) = concatMap varDataPlus vs

varDataPlusPi :: [(Identifier, CodePlus)] -> [Identifier]
varDataPlusPi [] = []
varDataPlusPi ((x, n):xns) =
  varCodePlus n ++ filterPlus (/= x) (varDataPlusPi xns)

varDataPlusSigma :: [IdentifierPlus] -> [Identifier] -> [Identifier]
varDataPlusSigma [] xs = xs
varDataPlusSigma ((x, p):xps) xs =
  varDataPlus p ++ filterPlus (/= x) (varDataPlusSigma xps xs)

varCodePlus :: CodePlus -> [Identifier]
varCodePlus (_, CodeTheta e) = varTheta e
varCodePlus (_, CodeEpsilonElim x v branchList) = do
  let (_, es) = unzip branchList
  varDataPlus v ++ filterPlus (/= x) (concatMap varCodePlus es)
varCodePlus (_, CodePiElimDownElim v es) =
  varDataPlus v ++ concatMap varCodePlus es
varCodePlus (_, CodeSigmaElim xs v e) =
  varDataPlus v ++ filterPlus (`notElem` xs) (varCodePlus e)
varCodePlus (_, CodeUpIntro v) = varDataPlus v
varCodePlus (_, CodeCopyN v1 v2) = varDataPlus v1 ++ varDataPlus v2
varCodePlus (_, CodeTransposeN v vs) = varDataPlus v ++ concatMap varDataPlus vs

varTheta :: Theta -> [Identifier]
varTheta = undefined

filterPlus :: (Identifier -> Bool) -> [Identifier] -> [Identifier]
filterPlus = undefined

type SubstDataPlus = [IdentifierPlus]

substDataPlus :: SubstDataPlus -> DataPlus -> DataPlus
substDataPlus _ (m, DataTheta x) = (m, DataTheta x)
substDataPlus sub (m, DataUpsilon s) =
  fromMaybe (m, DataUpsilon s) (lookup s sub)
substDataPlus _ (m, DataEpsilonIntro l p) = (m, DataEpsilonIntro l p)
substDataPlus sub (m, DataDownIntroPiIntro xs e) = do
  let sub' = filter (\(y, _) -> y `notElem` xs) sub
  let e' = substCodePlus sub' e
  (m, DataDownIntroPiIntro xs e')
substDataPlus sub (m, DataSigmaIntro vs) = do
  let vs' = map (substDataPlus sub) vs
  (m, DataSigmaIntro vs')

substCodePlus :: SubstDataPlus -> CodePlus -> CodePlus
substCodePlus sub (m, CodeTheta theta) = do
  let theta' = substTheta sub theta
  (m, CodeTheta theta')
substCodePlus sub (m, CodeEpsilonElim x v branchList) = do
  let v' = substDataPlus sub v
  let (cs, es) = unzip branchList
  let es' = map (substCodePlus (filter (\(y, _) -> y /= x) sub)) es
  let branchList' = zip cs es'
  (m, CodeEpsilonElim x v' branchList')
substCodePlus sub (m, CodePiElimDownElim v es) = do
  let v' = substDataPlus sub v
  let es' = map (substCodePlus sub) es
  (m, CodePiElimDownElim v' es')
substCodePlus sub (m, CodeSigmaElim xs v e) = do
  let v' = substDataPlus sub v
  let (xs', e') = substDataPlusSigmaElim sub xs e
  (m, CodeSigmaElim xs' v' e')
substCodePlus sub (m, CodeUpIntro v) = do
  let v' = substDataPlus sub v
  (m, CodeUpIntro v')
substCodePlus sub (m, CodeCopyN v1 v2) = do
  let v1' = substDataPlus sub v1
  let v2' = substDataPlus sub v2
  (m, CodeCopyN v1' v2')
substCodePlus sub (m, CodeTransposeN v vs) = do
  let v' = substDataPlus sub v
  let vs' = map (substDataPlus sub) vs
  (m, CodeTransposeN v' vs')

substTheta :: SubstDataPlus -> Theta -> Theta
substTheta sub (ThetaArith a t v1 v2) = do
  let v1' = substDataPlus sub v1
  let v2' = substDataPlus sub v2
  ThetaArith a t v1' v2'
substTheta sub (ThetaPrint v) = ThetaPrint $ substDataPlus sub v

substDataPlusPi ::
     SubstDataPlus -> [(Identifier, CodePlus)] -> [(Identifier, CodePlus)]
substDataPlusPi _ [] = []
substDataPlusPi sub ((x, p):xns) = do
  let xns' = substDataPlusPi (filter (\(y, _) -> y /= x) sub) xns
  (x, substCodePlus sub p) : xns'

substDataPlusSigma :: SubstDataPlus -> [IdentifierPlus] -> [IdentifierPlus]
substDataPlusSigma _ [] = []
substDataPlusSigma sub ((x, p):xps) = do
  let xps' = substDataPlusSigma (filter (\(y, _) -> y /= x) sub) xps
  (x, substDataPlus sub p) : xps'

substCodePlusPi ::
     SubstDataPlus
  -> [IdentifierPlus]
  -> CodePlus
  -> ([IdentifierPlus], CodePlus)
substCodePlusPi sub [] n = ([], substCodePlus sub n)
substCodePlusPi sub ((x, p):xps) n = do
  let (xps', n') = substCodePlusPi (filter (\(y, _) -> y /= x) sub) xps n
  let p' = substDataPlus sub p
  ((x, p') : xps', n')

substDataPlusSigmaElim ::
     SubstDataPlus -> [Identifier] -> CodePlus -> ([Identifier], CodePlus)
substDataPlusSigmaElim sub [] e = do
  let e' = substCodePlus sub e
  ([], e')
substDataPlusSigmaElim sub (x:xs) e = do
  let sub' = filter (\(y, _) -> y /= x) sub
  let (xs', e') = substDataPlusSigmaElim sub' xs e
  (x : xs', e')
