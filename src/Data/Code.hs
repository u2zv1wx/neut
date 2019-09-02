module Data.Code where

import           Data.Basic
import           Data.Maybe (fromMaybe)

data Data
  = DataTau
  | DataTheta Identifier -- global variable
  | DataUpsilon Identifier
  | DataEpsilon Identifier
  | DataEpsilonIntro Literal
                     DataPlus
  | DataDownPi [(Identifier, CodePlus)]
  | DataDownIntroPiIntro [Identifier]
                         CodePlus
  | DataSigma [(Identifier, DataPlus)]
  | DataSigmaIntro [DataPlus]
  deriving (Show)

data Code
  = CodeTheta Theta
  | CodeEpsilonElim Identifier
                    DataPlus
                    [(Case, CodePlus)]
  | CodePiElimDownElim DataPlus
                       [CodePlus]
  | CodeSigmaElim [Identifier]
                  DataPlus
                  CodePlus
  | CodeUp DataPlus
  | CodeUpIntro DataPlus
  deriving (Show)

data Theta
  = ThetaArith Arith
               DataPlus
               DataPlus
               DataPlus
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
varDataPlus (_, DataTau) = []
varDataPlus (_, DataTheta _) = []
varDataPlus (_, DataUpsilon x) = [x]
varDataPlus (_, DataEpsilon _) = []
varDataPlus (_, DataEpsilonIntro _ p) = varDataPlus p
varDataPlus (_, DataDownPi xns) = varDataPlusPi xns
varDataPlus (_, DataDownIntroPiIntro xs e) =
  filter (`notElem` xs) $ varCodePlus e
varDataPlus (_, DataSigma xps) = varDataPlusSigma xps []
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
varCodePlus (_, CodeUp v) = varDataPlus v
varCodePlus (_, CodeUpIntro v) = varDataPlus v

varTheta :: Theta -> [Identifier]
varTheta = undefined

filterPlus :: (Identifier -> Bool) -> [Identifier] -> [Identifier]
filterPlus = undefined

type SubstDataPlus = [IdentifierPlus]

substDataPlus :: SubstDataPlus -> DataPlus -> DataPlus
substDataPlus _ (m, DataTau) = (m, DataTau)
substDataPlus _ (m, DataTheta x) = (m, DataTheta x)
substDataPlus sub (m, DataUpsilon s) =
  fromMaybe (m, DataUpsilon s) (lookup s sub)
substDataPlus _ (m, DataEpsilon x) = (m, DataEpsilon x)
substDataPlus sub (m, DataEpsilonIntro l p) = do
  let p' = substDataPlus sub p
  (m, DataEpsilonIntro l p')
substDataPlus sub (m, DataDownPi xns) = do
  let xns' = substDataPlusPi sub xns
  (m, DataDownPi xns')
substDataPlus sub (m, DataDownIntroPiIntro xs e) = do
  let sub' = filter (\(y, _) -> y `notElem` xs) sub
  let e' = substCodePlus sub' e
  (m, DataDownIntroPiIntro xs e')
substDataPlus sub (m, DataSigma xps) = do
  let xps' = substDataPlusSigma sub xps
  (m, DataSigma xps')
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
substCodePlus sub (m, CodeUp v) = do
  let v' = substDataPlus sub v
  (m, CodeUp v')
substCodePlus sub (m, CodeUpIntro v) = do
  let v' = substDataPlus sub v
  (m, CodeUpIntro v')

substTheta :: SubstDataPlus -> Theta -> Theta
substTheta sub (ThetaArith a t v1 v2) = do
  let t' = substDataPlus sub t
  let v1' = substDataPlus sub v1
  let v2' = substDataPlus sub v2
  ThetaArith a t' v1' v2'
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

checkSanityData :: DataPlus -> Bool
checkSanityData (_, DataEpsilonIntro _ p) = null $ varDataPlus p
checkSanityData (_, DataSigma xts) = do
  let (xs, ts) = unzip xts
  all (`elem` xs) (concatMap varDataPlus ts) -- sigma must be closed
checkSanityData _ = True

checkSanityCode :: CodePlus -> Bool
checkSanityCode (_, CodeTheta _) = True
checkSanityCode (_, CodeEpsilonElim _ d branchList) = do
  let (_, es) = unzip branchList
  checkSanityData d && all checkSanityCode es
checkSanityCode (_, CodePiElimDownElim d es) =
  checkSanityData d && all checkSanityCode es
checkSanityCode (_, CodeSigmaElim _ v e) =
  checkSanityData v && checkSanityCode e
checkSanityCode (_, CodeUp v) = checkSanityData v
checkSanityCode (_, CodeUpIntro v) = checkSanityData v
