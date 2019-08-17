module Data.Code where

import           Data.Maybe (fromMaybe)

import           Data.Basic

data Data
  = DataTau
  | DataTheta Identifier
  | DataUpsilon Identifier
  | DataEpsilon Identifier
  | DataEpsilonIntro Literal
  | DataDownPi [IdentifierPlus]
               CodePlus
  | DataSigma [IdentifierPlus]
  | DataSigmaIntro [DataPlus]
  deriving (Show)

data Code
  = CodeEpsilonElim IdentifierPlus
                    DataPlus
                    [(Case, CodePlus)]
  | CodePiElimDownElim DataPlus
                       [DataPlus]
  | CodeSigmaElim [IdentifierPlus]
                  DataPlus
                  CodePlus
  | CodeUp DataPlus
  | CodeUpIntro DataPlus
  | CodeUpElim IdentifierPlus
               CodePlus
               CodePlus
  deriving (Show)

type IdentifierPlus = (Identifier, DataPlus)

data DataMeta
  = DataMetaTerminal (Maybe (Int, Int))
  | DataMetaNonTerminal DataPlus
                        (Maybe (Int, Int))
  deriving (Show)

data CodeMeta =
  CodeMetaNonTerminal CodePlus
                      (Maybe (Int, Int))
  deriving (Show)

type DataPlus = (DataMeta, Data)

type CodePlus = (CodeMeta, Code)

varDataPlus :: DataPlus -> [Identifier]
varDataPlus (_, DataTau)            = []
varDataPlus (_, DataTheta _)        = []
varDataPlus (_, DataUpsilon x)      = [x]
varDataPlus (_, DataEpsilon _)      = []
varDataPlus (_, DataEpsilonIntro _) = []
varDataPlus (_, DataDownPi xps n)   = varCodePlusPi xps n
varDataPlus (_, DataSigma xps)      = varDataPlusSigma xps
varDataPlus (_, DataSigmaIntro vs)  = concatMap varDataPlus vs

varDataPlusSigma :: [IdentifierPlus] -> [Identifier]
varDataPlusSigma [] = []
varDataPlusSigma ((x, p):xps) =
  varDataPlus p ++ filter (/= x) (varDataPlusSigma xps)

varCodePlus :: CodePlus -> [Identifier]
varCodePlus (_, CodeEpsilonElim (x, _) v branchList) = do
  let (_, es) = unzip branchList
  varDataPlus v ++ filter (/= x) (concatMap varCodePlus es)
varCodePlus (_, CodePiElimDownElim v vs) =
  varDataPlus v ++ concatMap varDataPlus vs
varCodePlus (_, CodeSigmaElim xps v e) =
  varDataPlus v ++ filter (`notElem` map fst xps) (varCodePlus e)
varCodePlus (_, CodeUp p) = varDataPlus p
varCodePlus (_, CodeUpIntro v) = varDataPlus v
varCodePlus (_, CodeUpElim (x, _) e1 e2) =
  varCodePlus e1 ++ filter (/= x) (varCodePlus e2)

varCodePlusPi :: [IdentifierPlus] -> CodePlus -> [Identifier]
varCodePlusPi [] n = varCodePlus n
varCodePlusPi ((x, p):xps) n =
  varDataPlus p ++ filter (/= x) (varCodePlusPi xps n)

type SubstDataPlus = [IdentifierPlus]

substDataPlus :: SubstDataPlus -> DataPlus -> DataPlus
substDataPlus sub (m, DataTau) = do
  let m' = substDataMeta sub m
  (m', DataTau)
substDataPlus sub (m, DataUpsilon s) = do
  let m' = substDataMeta sub m
  fromMaybe (m', DataUpsilon s) (lookup s sub)
substDataPlus sub (m, DataTheta s) = do
  let m' = substDataMeta sub m
  (m', DataTheta s)
substDataPlus sub (m, DataEpsilon k) = do
  let m' = substDataMeta sub m
  (m', DataEpsilon k)
substDataPlus sub (m, DataEpsilonIntro l) = do
  let m' = substDataMeta sub m
  (m', DataEpsilonIntro l)
substDataPlus sub (m, DataDownPi xps n) = do
  let (xps', n') = substCodePlusPi sub xps n
  let m' = substDataMeta sub m
  (m', DataDownPi xps' n')
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

substCodePlus :: SubstDataPlus -> CodePlus -> CodePlus
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
substCodePlus sub (m, CodeSigmaElim xps v e) = do
  let v' = substDataPlus sub v
  let (xps', e') = substDataPlusSigmaElim sub xps e
  let m' = substCodeMeta sub m
  (m', CodeSigmaElim xps' v' e')
substCodePlus sub (m, CodeUp p) = do
  let p' = substDataPlus sub p
  let m' = substCodeMeta sub m
  (m', CodeUp p')
substCodePlus sub (m, CodeUpIntro v) = do
  let v' = substDataPlus sub v
  let m' = substCodeMeta sub m
  (m', CodeUpIntro v')
substCodePlus sub (m, CodeUpElim (x, p) e1 e2) = do
  let p' = substDataPlus sub p
  let e1' = substCodePlus sub e1
  let e2' = substCodePlus (filter (\(y, _) -> y /= x) sub) e2
  let m' = substCodeMeta sub m
  (m', CodeUpElim (x, p') e1' e2')

substCodeMeta :: SubstDataPlus -> CodeMeta -> CodeMeta
substCodeMeta sub (CodeMetaNonTerminal n ml) =
  CodeMetaNonTerminal (substCodePlus sub n) ml

substDataPlusSigma :: SubstDataPlus -> [IdentifierPlus] -> [IdentifierPlus]
substDataPlusSigma _ [] = []
substDataPlusSigma sub ((x, p):xps) = do
  let xps' = substDataPlusSigma (filter (\(y, _) -> y /= x) sub) xps
  let p' = substDataPlus sub p
  (x, p') : xps'

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
     SubstDataPlus
  -> [IdentifierPlus]
  -> CodePlus
  -> ([IdentifierPlus], CodePlus)
substDataPlusSigmaElim sub [] e = do
  let e' = substCodePlus sub e
  ([], e')
substDataPlusSigmaElim sub ((x, p):xps) e = do
  let sub' = filter (\(y, _) -> y /= x) sub
  let (xps', e') = substDataPlusSigmaElim sub' xps e
  let p' = substDataPlus sub p
  ((x, p') : xps', e')
