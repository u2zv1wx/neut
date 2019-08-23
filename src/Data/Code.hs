module Data.Code where

import           Data.Maybe (fromMaybe)

import           Data.Basic

data Data
  = DataTau
  | DataUpsilon Identifier
  | DataEpsilon Identifier
  | DataEpsilonIntro Literal
  | DataDownIntroPiIntro [IdentifierPlus]
                         CodePlus
  | DataSigma [IdentifierPlus]
              DataPlus
  | DataSigmaIntro [DataPlus]
  | DataDown CodePlus
  deriving (Show)

data Code
  = CodeTau
  | CodeTheta Theta
  | CodeEpsilonElim IdentifierPlus
                    DataPlus
                    [(Case, CodePlus)]
  | CodePi [IdentifierPlus]
           CodePlus
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
  | CodeMu IdentifierPlus
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

varDataPlus :: DataPlus -> [Identifier]
varDataPlus (_, DataTau) = []
varDataPlus (_, DataUpsilon x) = [x]
varDataPlus (_, DataEpsilon _) = []
varDataPlus (_, DataEpsilonIntro _) = []
varDataPlus (_, DataDownIntroPiIntro xps e) =
  filter (`notElem` map fst xps) $
  concatMap (varDataPlus . snd) xps ++ varCodePlus e
varDataPlus (_, DataSigma xps p) = varDataPlusPiOrSigma xps (varDataPlus p)
varDataPlus (_, DataSigmaIntro vs) = concatMap varDataPlus vs
varDataPlus (_, DataDown n) = varCodePlus n

varDataPlusPiOrSigma :: [IdentifierPlus] -> [Identifier] -> [Identifier]
varDataPlusPiOrSigma [] xs = xs
varDataPlusPiOrSigma ((x, p):xps) xs =
  varDataPlus p ++ filter (/= x) (varDataPlusPiOrSigma xps xs)

varCodePlus :: CodePlus -> [Identifier]
varCodePlus (_, CodeTau) = []
varCodePlus (_, CodeTheta e) = varTheta e
varCodePlus (_, CodeEpsilonElim (x, _) v branchList) = do
  let (_, es) = unzip branchList
  varDataPlus v ++ filter (/= x) (concatMap varCodePlus es)
varCodePlus (_, CodePi xps n) = varDataPlusPiOrSigma xps (varCodePlus n)
varCodePlus (_, CodePiElimDownElim v vs) =
  varDataPlus v ++ concatMap varDataPlus vs
varCodePlus (_, CodeSigmaElim xps v e) =
  varDataPlus v ++ filter (`notElem` map fst xps) (varCodePlus e)
varCodePlus (_, CodeUp p) = varDataPlus p
varCodePlus (_, CodeUpIntro v) = varDataPlus v
varCodePlus (_, CodeUpElim (x, _) e1 e2) =
  varCodePlus e1 ++ filter (/= x) (varCodePlus e2)
varCodePlus (_, CodeMu (x, _) e) = filter (/= x) $ varCodePlus e

varDataPlusPi :: [IdentifierPlus] -> DataPlus -> [Identifier]
varDataPlusPi [] n = varDataPlus n
varDataPlusPi ((x, p):xps) n =
  varDataPlus p ++ filter (/= x) (varDataPlusPi xps n)

varTheta :: Theta -> [Identifier]
varTheta = undefined

type SubstDataPlus = [IdentifierPlus]

substDataPlus :: SubstDataPlus -> DataPlus -> DataPlus
substDataPlus sub (m, DataTau) = do
  let m' = substDataMeta sub m
  (m', DataTau)
substDataPlus sub (m, DataUpsilon s) = do
  let m' = substDataMeta sub m
  fromMaybe (m', DataUpsilon s) (lookup s sub)
substDataPlus sub (m, DataEpsilon k) = do
  let m' = substDataMeta sub m
  (m', DataEpsilon k)
substDataPlus sub (m, DataEpsilonIntro l) = do
  let m' = substDataMeta sub m
  (m', DataEpsilonIntro l)
substDataPlus sub (m, DataDownIntroPiIntro xps e) = do
  let (xps', e') = substCodePlusPi sub xps e
  let m' = substDataMeta sub m
  (m', DataDownIntroPiIntro xps' e')
substDataPlus sub (m, DataSigma xps p) = do
  let (xps', p') = substDataPlusSigma sub xps p
  let m' = substDataMeta sub m
  (m', DataSigma xps' p')
substDataPlus sub (m, DataSigmaIntro vs) = do
  let vs' = map (substDataPlus sub) vs
  let m' = substDataMeta sub m
  (m', DataSigmaIntro vs')
substDataPlus sub (m, DataDown n) = do
  let n' = substCodePlus sub n
  let m' = substDataMeta sub m
  (m', DataDown n')

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
substCodePlus sub (m, CodePi xps n) = do
  let (xps', n') = substDataPlusPi sub xps n
  let m' = substCodeMeta sub m
  (m', CodePi xps' n')
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
substCodePlus sub (m, CodeMu (x, p) e) = do
  let p' = substDataPlus sub p
  let e' = substCodePlus (filter (\(y, _) -> y /= x) sub) e
  let m' = substCodeMeta sub m
  (m', CodeMu (x, p') e')

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

substDataPlusSigma ::
     SubstDataPlus
  -> [IdentifierPlus]
  -> DataPlus
  -> ([IdentifierPlus], DataPlus)
substDataPlusSigma sub [] q = ([], substDataPlus sub q)
substDataPlusSigma sub ((x, p):xps) q = do
  let (xps', q') = substDataPlusSigma (filter (\(y, _) -> y /= x) sub) xps q
  ((x, substDataPlus sub p) : xps', q')

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
-- data Data
--   = DataTau
--   | DataTheta Identifier
--   | DataUpsilon Identifier
--   | DataEpsilon Identifier
--   | DataEpsilonIntro Literal
--   | DataDownPi [IdentifierPlus]
--                CodePlus
--   | DataSigma [IdentifierPlus]
--   | DataSigmaIntro [DataPlus]
--   deriving (Show)
-- data Code
--   = CodeTau
--   | CodeEpsilonElim IdentifierPlus
--                     DataPlus
--                     [(Case, CodePlus)]
--   | CodePiElimDownElim DataPlus
--                        [DataPlus]
--   | CodeSigmaElim [IdentifierPlus]
--                   DataPlus
--                   CodePlus
--   | CodeUp DataPlus
--   | CodeUpIntro DataPlus
--   | CodeUpElim IdentifierPlus
--                CodePlus
--                CodePlus
--   deriving (Show)
-- type IdentifierPlus = (Identifier, DataPlus)
-- data DataMeta
--   = DataMetaTerminal (Maybe (Int, Int))
--   | DataMetaNonTerminal DataPlus
--                         (Maybe (Int, Int))
--   deriving (Show)
-- data CodeMeta =
--   CodeMetaNonTerminal CodePlus
--                       (Maybe (Int, Int))
--   deriving (Show)
-- type DataPlus = (DataMeta, Data)
-- type CodePlus = (CodeMeta, Code)
-- varDataPlus :: DataPlus -> [Identifier]
-- varDataPlus (_, DataTau)            = []
-- varDataPlus (_, DataTheta _)        = []
-- varDataPlus (_, DataUpsilon x)      = [x]
-- varDataPlus (_, DataEpsilon _)      = []
-- varDataPlus (_, DataEpsilonIntro _) = []
-- varDataPlus (_, DataDownPi xps n)   = varCodePlusPi xps n
-- varDataPlus (_, DataSigma xps)      = varDataPlusSigma xps
-- varDataPlus (_, DataSigmaIntro vs)  = concatMap varDataPlus vs
-- varDataPlusSigma :: [IdentifierPlus] -> [Identifier]
-- varDataPlusSigma [] = []
-- varDataPlusSigma ((x, p):xps) =
--   varDataPlus p ++ filter (/= x) (varDataPlusSigma xps)
-- varCodePlus :: CodePlus -> [Identifier]
-- varCodePlus (_, CodeEpsilonElim (x, _) v branchList) = do
--   let (_, es) = unzip branchList
--   varDataPlus v ++ filter (/= x) (concatMap varCodePlus es)
-- varCodePlus (_, CodePiElimDownElim v vs) =
--   varDataPlus v ++ concatMap varDataPlus vs
-- varCodePlus (_, CodeSigmaElim xps v e) =
--   varDataPlus v ++ filter (`notElem` map fst xps) (varCodePlus e)
-- varCodePlus (_, CodeUp p) = varDataPlus p
-- varCodePlus (_, CodeUpIntro v) = varDataPlus v
-- varCodePlus (_, CodeUpElim (x, _) e1 e2) =
--   varCodePlus e1 ++ filter (/= x) (varCodePlus e2)
-- varCodePlusPi :: [IdentifierPlus] -> CodePlus -> [Identifier]
-- varCodePlusPi [] n = varCodePlus n
-- varCodePlusPi ((x, p):xps) n =
--   varDataPlus p ++ filter (/= x) (varCodePlusPi xps n)
-- type SubstDataPlus = [IdentifierPlus]
-- substDataPlus :: SubstDataPlus -> DataPlus -> DataPlus
-- substDataPlus sub (m, DataTau) = do
--   let m' = substDataMeta sub m
--   (m', DataTau)
-- substDataPlus sub (m, DataUpsilon s) = do
--   let m' = substDataMeta sub m
--   fromMaybe (m', DataUpsilon s) (lookup s sub)
-- substDataPlus sub (m, DataTheta s) = do
--   let m' = substDataMeta sub m
--   (m', DataTheta s)
-- substDataPlus sub (m, DataEpsilon k) = do
--   let m' = substDataMeta sub m
--   (m', DataEpsilon k)
-- substDataPlus sub (m, DataEpsilonIntro l) = do
--   let m' = substDataMeta sub m
--   (m', DataEpsilonIntro l)
-- substDataPlus sub (m, DataDownPi xps n) = do
--   let (xps', n') = substCodePlusPi sub xps n
--   let m' = substDataMeta sub m
--   (m', DataDownPi xps' n')
-- substDataPlus sub (m, DataSigma xps) = do
--   let xps' = substDataPlusSigma sub xps
--   let m' = substDataMeta sub m
--   (m', DataSigma xps')
-- substDataPlus sub (m, DataSigmaIntro vs) = do
--   let vs' = map (substDataPlus sub) vs
--   let m' = substDataMeta sub m
--   (m', DataSigmaIntro vs')
-- substDataMeta :: SubstDataPlus -> DataMeta -> DataMeta
-- substDataMeta _ (DataMetaTerminal ml) = DataMetaTerminal ml
-- substDataMeta sub (DataMetaNonTerminal p ml) =
--   DataMetaNonTerminal (substDataPlus sub p) ml
-- substCodePlus :: SubstDataPlus -> CodePlus -> CodePlus
-- substCodePlus sub (m, CodeEpsilonElim (x, p) v branchList) = do
--   let p' = substDataPlus sub p
--   let v' = substDataPlus sub v
--   let (cs, es) = unzip branchList
--   let es' = map (substCodePlus (filter (\(y, _) -> y /= x) sub)) es
--   let branchList' = zip cs es'
--   let m' = substCodeMeta sub m
--   (m', CodeEpsilonElim (x, p') v' branchList')
-- substCodePlus sub (m, CodePiElimDownElim v vs) = do
--   let v' = substDataPlus sub v
--   let vs' = map (substDataPlus sub) vs
--   let m' = substCodeMeta sub m
--   (m', CodePiElimDownElim v' vs')
-- substCodePlus sub (m, CodeSigmaElim xps v e) = do
--   let v' = substDataPlus sub v
--   let (xps', e') = substDataPlusSigmaElim sub xps e
--   let m' = substCodeMeta sub m
--   (m', CodeSigmaElim xps' v' e')
-- substCodePlus sub (m, CodeUp p) = do
--   let p' = substDataPlus sub p
--   let m' = substCodeMeta sub m
--   (m', CodeUp p')
-- substCodePlus sub (m, CodeUpIntro v) = do
--   let v' = substDataPlus sub v
--   let m' = substCodeMeta sub m
--   (m', CodeUpIntro v')
-- substCodePlus sub (m, CodeUpElim (x, p) e1 e2) = do
--   let p' = substDataPlus sub p
--   let e1' = substCodePlus sub e1
--   let e2' = substCodePlus (filter (\(y, _) -> y /= x) sub) e2
--   let m' = substCodeMeta sub m
--   (m', CodeUpElim (x, p') e1' e2')
-- substCodeMeta :: SubstDataPlus -> CodeMeta -> CodeMeta
-- substCodeMeta sub (CodeMetaNonTerminal n ml) =
--   CodeMetaNonTerminal (substCodePlus sub n) ml
-- substDataPlusSigma :: SubstDataPlus -> [IdentifierPlus] -> [IdentifierPlus]
-- substDataPlusSigma _ [] = []
-- substDataPlusSigma sub ((x, p):xps) = do
--   let xps' = substDataPlusSigma (filter (\(y, _) -> y /= x) sub) xps
--   let p' = substDataPlus sub p
--   (x, p') : xps'
-- substCodePlusPi ::
--      SubstDataPlus
--   -> [IdentifierPlus]
--   -> CodePlus
--   -> ([IdentifierPlus], CodePlus)
-- substCodePlusPi sub [] n = ([], substCodePlus sub n)
-- substCodePlusPi sub ((x, p):xps) n = do
--   let (xps', n') = substCodePlusPi (filter (\(y, _) -> y /= x) sub) xps n
--   let p' = substDataPlus sub p
--   ((x, p') : xps', n')
-- substDataPlusSigmaElim ::
--      SubstDataPlus
--   -> [IdentifierPlus]
--   -> CodePlus
--   -> ([IdentifierPlus], CodePlus)
-- substDataPlusSigmaElim sub [] e = do
--   let e' = substCodePlus sub e
--   ([], e')
-- substDataPlusSigmaElim sub ((x, p):xps) e = do
--   let sub' = filter (\(y, _) -> y /= x) sub
--   let (xps', e') = substDataPlusSigmaElim sub' xps e
--   let p' = substDataPlus sub p
--   ((x, p') : xps', e')
