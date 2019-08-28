module Data.Code where

import           Data.Maybe (fromMaybe)

import           Data.Basic

data Data
  = DataTheta Identifier -- global variable
  | DataUpsilon Identifier
  | DataEpsilonIntro Literal
  | DataSigma [IdentifierPlus]
  | DataSigmaIntro [DataPlus]
  | DataSigmaIntroN DataPlus
                    DataPlus
  deriving (Show)

data Code
  = CodeTau
  | CodeTheta Theta
  | CodeEpsilonElim IdentifierPlus
                    DataPlus
                    [(Case, CodePlus)]
  | CodePiElimDownElim DataPlus
                       [DataPlus]
  | CodeSigmaElim [Identifier]
                  DataPlus
                  CodePlus
  | CodeUp DataPlus
  | CodeUpIntro DataPlus
  | CodeUpElim Identifier
               CodePlus
               CodePlus
  deriving (Show)

data Theta
  = ThetaArith Arith
               DataPlus
               DataPlus
  | ThetaPrint DataPlus
  deriving (Show)

type IdentifierPlus = (Identifier, DataPlus)

data DataMeta
  = DataMetaTerminal (Maybe (Int, Int))
  | DataMetaNonTerminal DataPlus
                        (Maybe (Int, Int))
  deriving (Show)

data CodeMeta
  = CodeMetaTerminal (Maybe (Int, Int))
  | CodeMetaNonTerminal CodePlus
                        (Maybe (Int, Int))
  deriving (Show)

-- FIXME: (Data, DataMeta)としたほうがe : Aに揃って読みやすいかもしれない。
type DataPlus = (DataMeta, Data)

type CodePlus = (CodeMeta, Code)

obtainInfoCodeMeta :: CodeMeta -> (CodePlus, Maybe (Int, Int))
obtainInfoCodeMeta (CodeMetaTerminal ml) = ((CodeMetaTerminal ml, CodeTau), ml)
obtainInfoCodeMeta (CodeMetaNonTerminal t ml) = (t, ml)

-- fixme: undefind ~> exponentTrivial
obtainInfoDataMeta :: DataMeta -> (DataPlus, Maybe (Int, Int))
obtainInfoDataMeta (DataMetaTerminal ml) =
  ((DataMetaTerminal ml, undefined), ml)
obtainInfoDataMeta (DataMetaNonTerminal t ml) = (t, ml)

varDataPlus :: DataPlus -> [IdentifierPlus]
varDataPlus (_, DataTheta _)        = []
varDataPlus (m, DataUpsilon x)      = [(x, fst $ obtainInfoDataMeta m)]
varDataPlus (_, DataEpsilonIntro _) = []
varDataPlus (_, DataSigma xps)      = varDataPlusPiOrSigma xps []
varDataPlus (_, DataSigmaIntro vs)  = concatMap varDataPlus vs

varDataPlusPiOrSigma :: [IdentifierPlus] -> [IdentifierPlus] -> [IdentifierPlus]
varDataPlusPiOrSigma [] xs = xs
varDataPlusPiOrSigma ((x, p):xps) xs =
  varDataPlus p ++ filterPlus (/= x) (varDataPlusPiOrSigma xps xs)

varCodePlus :: CodePlus -> [IdentifierPlus]
varCodePlus (_, CodeTau) = []
varCodePlus (_, CodeTheta e) = varTheta e
varCodePlus (_, CodeEpsilonElim (x, _) v branchList) = do
  let (_, es) = unzip branchList
  varDataPlus v ++ filterPlus (/= x) (concatMap varCodePlus es)
varCodePlus (_, CodePiElimDownElim v vs) =
  varDataPlus v ++ concatMap varDataPlus vs
varCodePlus (_, CodeSigmaElim xs v e) =
  varDataPlus v ++ filterPlus (`notElem` xs) (varCodePlus e)
varCodePlus (_, CodeUp p) = varDataPlus p
varCodePlus (_, CodeUpIntro v) = varDataPlus v
varCodePlus (_, CodeUpElim x e1 e2) =
  varCodePlus e1 ++ filterPlus (/= x) (varCodePlus e2)

varDataPlusPi :: [IdentifierPlus] -> DataPlus -> [IdentifierPlus]
varDataPlusPi [] n = varDataPlus n
varDataPlusPi ((x, p):xps) n =
  varDataPlus p ++ filterPlus (/= x) (varDataPlusPi xps n)

varTheta :: Theta -> [IdentifierPlus]
varTheta = undefined

filterPlus :: (Identifier -> Bool) -> [IdentifierPlus] -> [IdentifierPlus]
filterPlus = undefined

type SubstDataPlus = [IdentifierPlus]

substDataPlus :: SubstDataPlus -> DataPlus -> DataPlus
substDataPlus sub (m, DataTheta x) = do
  let m' = substDataMeta sub m
  (m', DataTheta x)
substDataPlus sub (m, DataUpsilon s) = do
  let m' = substDataMeta sub m
  fromMaybe (m', DataUpsilon s) (lookup s sub)
substDataPlus sub (m, DataEpsilonIntro l) = do
  let m' = substDataMeta sub m
  (m', DataEpsilonIntro l)
substDataPlus sub (m, DataSigma xps) = do
  let xps' = substDataPlusSigma sub xps
  let m' = substDataMeta sub m
  (m', DataSigma xps')
substDataPlus sub (m, DataSigmaIntro vs) = do
  let vs' = map (substDataPlus sub) vs
  let m' = substDataMeta sub m
  (m', DataSigmaIntro vs')

substDataMeta :: SubstDataPlus -> DataMeta -> DataMeta
substDataMeta _ (DataMetaTerminal ml) = DataMetaTerminal ml
substDataMeta sub (DataMetaNonTerminal p ml) =
  DataMetaNonTerminal (substDataPlus sub p) ml

substCodeMeta :: SubstDataPlus -> CodeMeta -> CodeMeta
substCodeMeta _ (CodeMetaTerminal ml) = CodeMetaTerminal ml
substCodeMeta sub (CodeMetaNonTerminal p ml) =
  CodeMetaNonTerminal (substCodePlus sub p) ml

substCodePlus :: SubstDataPlus -> CodePlus -> CodePlus
substCodePlus sub (m, CodeTau) = do
  let m' = substCodeMeta sub m
  (m', CodeTau)
substCodePlus sub (m, CodeTheta theta) = do
  let m' = substCodeMeta sub m
  let theta' = substTheta sub theta
  (m', CodeTheta theta')
substCodePlus sub (m, CodeEpsilonElim (x, p) v branchList) = do
  let p' = substDataPlus sub p
  let v' = substDataPlus sub v
  let (cs, es) = unzip branchList
  let es' = map (substCodePlus (filter (\(y, _) -> y /= x) sub)) es
  let branchList' = zip cs es'
  let m' = substCodeMeta sub m
  (m', CodeEpsilonElim (x, p') v' branchList')
substCodePlus sub (m, CodePiElimDownElim v vs) = do
  let v' = substDataPlus sub v
  let vs' = map (substDataPlus sub) vs
  let m' = substCodeMeta sub m
  (m', CodePiElimDownElim v' vs')
substCodePlus sub (m, CodeSigmaElim xs v e) = do
  let v' = substDataPlus sub v
  let (xs', e') = substDataPlusSigmaElim sub xs e
  let m' = substCodeMeta sub m
  (m', CodeSigmaElim xs' v' e')
substCodePlus sub (m, CodeUp p) = do
  let p' = substDataPlus sub p
  let m' = substCodeMeta sub m
  (m', CodeUp p')
substCodePlus sub (m, CodeUpIntro v) = do
  let v' = substDataPlus sub v
  let m' = substCodeMeta sub m
  (m', CodeUpIntro v')
substCodePlus sub (m, CodeUpElim x e1 e2) = do
  let e1' = substCodePlus sub e1
  let e2' = substCodePlus (filter (\(y, _) -> y /= x) sub) e2
  let m' = substCodeMeta sub m
  (m', CodeUpElim x e1' e2')

substTheta :: SubstDataPlus -> Theta -> Theta
substTheta sub (ThetaArith a v1 v2) = do
  let v1' = substDataPlus sub v1
  let v2' = substDataPlus sub v2
  ThetaArith a v1' v2'
substTheta sub (ThetaPrint v) = ThetaPrint $ substDataPlus sub v

substDataPlusPiOrSigma :: SubstDataPlus -> [IdentifierPlus] -> [IdentifierPlus]
substDataPlusPiOrSigma _ [] = []
substDataPlusPiOrSigma sub ((x, p):xps) = do
  let xps' = substDataPlusPiOrSigma (filter (\(y, _) -> y /= x) sub) xps
  let p' = substDataPlus sub p
  (x, p') : xps'

substDataPlusPi ::
     SubstDataPlus
  -> [IdentifierPlus]
  -> CodePlus
  -> ([IdentifierPlus], CodePlus)
substDataPlusPi sub [] n = ([], substCodePlus sub n)
substDataPlusPi sub ((x, p):xps) n = do
  let (xps', n') = substDataPlusPi (filter (\(y, _) -> y /= x) sub) xps n
  ((x, substDataPlus sub p) : xps', n')

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
