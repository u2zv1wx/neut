module Data.LowCode where

import           Data.Basic
import           Data.Maybe (fromMaybe)

data LowData
  = LowDataTheta Identifier -- global variable
  | LowDataUpsilon Identifier
  | LowDataEpsilonIntro Literal
                        LowType
  | LowDataSigmaIntro [LowDataPlus]
  deriving (Show)

data LowCode
  = LowCodeTheta LowDataTheta
  | LowCodeEpsilonElim Identifier
                       LowDataPlus
                       [(Case, LowCodePlus)]
  | LowCodePiElimDownElim LowDataPlus
                          [LowCodePlus]
  | LowCodeSigmaElim [Identifier]
                     LowDataPlus
                     LowCodePlus
  | LowCodeUpIntro LowDataPlus
  | LowCodeCopyN LowDataPlus
                 LowDataPlus
  | LowCodeTransposeN LowDataPlus -- Supposed to be a natural number `n`
                      [LowDataPlus] -- List of sigma-intro. Each sigma-intro has `n` elements.
  deriving (Show)

data LowDataTheta
  = LowDataThetaArith Arith
                      LowType
                      LowDataPlus
                      LowDataPlus
  | LowDataThetaPrint LowDataPlus
  deriving (Show)

type IdentifierPlus = (Identifier, LowDataPlus)

type LowCodeMeta = Maybe Loc

type LowDataPlus = (LowCodeMeta, LowData)

type LowCodePlus = (LowCodeMeta, LowCode)

toLowDataUpsilon :: (Identifier, Maybe Loc) -> LowDataPlus
toLowDataUpsilon (x, ml) = (ml, LowDataUpsilon x)

toLowDataUpsilon' :: Identifier -> LowDataPlus
toLowDataUpsilon' x = (Nothing, LowDataUpsilon x)

varLowDataPlus :: LowDataPlus -> [Identifier]
varLowDataPlus (_, LowDataTheta _)          = []
varLowDataPlus (_, LowDataUpsilon x)        = [x]
varLowDataPlus (_, LowDataEpsilonIntro _ _) = []
varLowDataPlus (_, LowDataSigmaIntro vs)    = concatMap varLowDataPlus vs

varLowDataPlusPiOrSigma :: [IdentifierPlus] -> [Identifier] -> [Identifier]
varLowDataPlusPiOrSigma [] xs = xs
varLowDataPlusPiOrSigma ((x, p):xps) xs =
  varLowDataPlus p ++ filterPlus (/= x) (varLowDataPlusPiOrSigma xps xs)

varLowCodePlus :: LowCodePlus -> [Identifier]
varLowCodePlus (_, LowCodeTheta e) = varTheta e
varLowCodePlus (_, LowCodeEpsilonElim x v branchList) = do
  let (_, es) = unzip branchList
  varLowDataPlus v ++ filterPlus (/= x) (concatMap varLowCodePlus es)
varLowCodePlus (_, LowCodePiElimDownElim v es) =
  varLowDataPlus v ++ concatMap varLowCodePlus es
varLowCodePlus (_, LowCodeSigmaElim xs v e) =
  varLowDataPlus v ++ filterPlus (`notElem` xs) (varLowCodePlus e)
varLowCodePlus (_, LowCodeUpIntro v) = varLowDataPlus v
varLowCodePlus (_, LowCodeCopyN v1 v2) = varLowDataPlus v1 ++ varLowDataPlus v2
varLowCodePlus (_, LowCodeTransposeN v vs) =
  varLowDataPlus v ++ concatMap varLowDataPlus vs

varLowDataPlusPi :: [IdentifierPlus] -> LowDataPlus -> [Identifier]
varLowDataPlusPi [] n = varLowDataPlus n
varLowDataPlusPi ((x, p):xps) n =
  varLowDataPlus p ++ filterPlus (/= x) (varLowDataPlusPi xps n)

varTheta :: LowDataTheta -> [Identifier]
varTheta = undefined

filterPlus :: (Identifier -> Bool) -> [Identifier] -> [Identifier]
filterPlus = undefined

type SubstLowDataPlus = [IdentifierPlus]

substLowDataPlus :: SubstLowDataPlus -> LowDataPlus -> LowDataPlus
substLowDataPlus _ (m, LowDataTheta x) = (m, LowDataTheta x)
substLowDataPlus sub (m, LowDataUpsilon s) =
  fromMaybe (m, LowDataUpsilon s) (lookup s sub)
substLowDataPlus _ (m, LowDataEpsilonIntro l lowType) =
  (m, LowDataEpsilonIntro l lowType)
substLowDataPlus sub (m, LowDataSigmaIntro vs) = do
  let vs' = map (substLowDataPlus sub) vs
  (m, LowDataSigmaIntro vs')

substLowCodePlus :: SubstLowDataPlus -> LowCodePlus -> LowCodePlus
substLowCodePlus sub (m, LowCodeTheta theta) = do
  let theta' = substTheta sub theta
  (m, LowCodeTheta theta')
substLowCodePlus sub (m, LowCodeEpsilonElim x v branchList) = do
  let v' = substLowDataPlus sub v
  let (cs, es) = unzip branchList
  let es' = map (substLowCodePlus (filter (\(y, _) -> y /= x) sub)) es
  let branchList' = zip cs es'
  (m, LowCodeEpsilonElim x v' branchList')
substLowCodePlus sub (m, LowCodePiElimDownElim v es) = do
  let v' = substLowDataPlus sub v
  let es' = map (substLowCodePlus sub) es
  (m, LowCodePiElimDownElim v' es')
substLowCodePlus sub (m, LowCodeSigmaElim xs v e) = do
  let v' = substLowDataPlus sub v
  let (xs', e') = substLowDataPlusSigmaElim sub xs e
  (m, LowCodeSigmaElim xs' v' e')
substLowCodePlus sub (m, LowCodeUpIntro v) = do
  let v' = substLowDataPlus sub v
  (m, LowCodeUpIntro v')
substLowCodePlus sub (m, LowCodeCopyN v1 v2) = do
  let v1' = substLowDataPlus sub v1
  let v2' = substLowDataPlus sub v2
  (m, LowCodeCopyN v1' v2')
substLowCodePlus sub (m, LowCodeTransposeN v vs) = do
  let v' = substLowDataPlus sub v
  let vs' = map (substLowDataPlus sub) vs
  (m, LowCodeTransposeN v' vs')

substTheta :: SubstLowDataPlus -> LowDataTheta -> LowDataTheta
substTheta sub (LowDataThetaArith a t v1 v2) = do
  let v1' = substLowDataPlus sub v1
  let v2' = substLowDataPlus sub v2
  LowDataThetaArith a t v1' v2'
substTheta sub (LowDataThetaPrint v) =
  LowDataThetaPrint $ substLowDataPlus sub v

substLowDataPlusPiOrSigma ::
     SubstLowDataPlus -> [IdentifierPlus] -> [IdentifierPlus]
substLowDataPlusPiOrSigma _ [] = []
substLowDataPlusPiOrSigma sub ((x, p):xps) = do
  let xps' = substLowDataPlusPiOrSigma (filter (\(y, _) -> y /= x) sub) xps
  let p' = substLowDataPlus sub p
  (x, p') : xps'

substLowDataPlusPi ::
     SubstLowDataPlus
  -> [IdentifierPlus]
  -> LowCodePlus
  -> ([IdentifierPlus], LowCodePlus)
substLowDataPlusPi sub [] n = ([], substLowCodePlus sub n)
substLowDataPlusPi sub ((x, p):xps) n = do
  let (xps', n') = substLowDataPlusPi (filter (\(y, _) -> y /= x) sub) xps n
  ((x, substLowDataPlus sub p) : xps', n')

substLowDataPlusSigma ::
     SubstLowDataPlus -> [IdentifierPlus] -> [IdentifierPlus]
substLowDataPlusSigma _ [] = []
substLowDataPlusSigma sub ((x, p):xps) = do
  let xps' = substLowDataPlusSigma (filter (\(y, _) -> y /= x) sub) xps
  (x, substLowDataPlus sub p) : xps'

substLowCodePlusPi ::
     SubstLowDataPlus
  -> [IdentifierPlus]
  -> LowCodePlus
  -> ([IdentifierPlus], LowCodePlus)
substLowCodePlusPi sub [] n = ([], substLowCodePlus sub n)
substLowCodePlusPi sub ((x, p):xps) n = do
  let (xps', n') = substLowCodePlusPi (filter (\(y, _) -> y /= x) sub) xps n
  let p' = substLowDataPlus sub p
  ((x, p') : xps', n')

substLowDataPlusSigmaElim ::
     SubstLowDataPlus
  -> [Identifier]
  -> LowCodePlus
  -> ([Identifier], LowCodePlus)
substLowDataPlusSigmaElim sub [] e = do
  let e' = substLowCodePlus sub e
  ([], e')
substLowDataPlusSigmaElim sub (x:xs) e = do
  let sub' = filter (\(y, _) -> y /= x) sub
  let (xs', e') = substLowDataPlusSigmaElim sub' xs e
  (x : xs', e')
