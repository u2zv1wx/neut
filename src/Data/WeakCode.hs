module Data.WeakCode where

import           Data.Maybe (fromMaybe)

import           Data.Basic

data WeakData
  = WeakDataTau
  | WeakDataUpsilon Identifier
  | WeakDataEpsilon Identifier
  | WeakDataEpsilonIntro Literal
  | WeakDataDownIntroPiIntro [IdentifierPlus]
                             WeakCodePlus
  | WeakDataSigma [IdentifierPlus]
                  WeakDataPlus
  | WeakDataSigmaIntro [WeakDataPlus]
  | WeakDataDown WeakCodePlus
  deriving (Show)

data WeakCode
  = WeakCodeTau
  | WeakCodeTheta WeakTheta
  | WeakCodeEpsilonElim IdentifierPlus
                        WeakDataPlus
                        [(Case, WeakCodePlus)]
  | WeakCodePi [IdentifierPlus]
               WeakCodePlus
  | WeakCodePiElimDownElim WeakDataPlus
                           [WeakDataPlus]
  | WeakCodeSigmaElim [IdentifierPlus]
                      WeakDataPlus
                      WeakCodePlus
  | WeakCodeUp WeakDataPlus
  | WeakCodeUpIntro WeakDataPlus
  | WeakCodeUpElim IdentifierPlus
                   WeakCodePlus
                   WeakCodePlus
  | WeakCodeMu IdentifierPlus
               WeakCodePlus
  deriving (Show)

data WeakTheta
  = WeakThetaArith Arith
                   WeakDataPlus
                   WeakDataPlus
  | WeakThetaPrint WeakDataPlus
  deriving (Show)

type IdentifierPlus = (Identifier, WeakDataPlus)

data WeakDataMeta
  = WeakDataMetaTerminal (Maybe (Int, Int))
  | WeakDataMetaNonTerminal WeakDataPlus
                            (Maybe (Int, Int))
  deriving (Show)

data WeakCodeMeta
  = WeakCodeMetaTerminal (Maybe (Int, Int))
  | WeakCodeMetaNonTerminal WeakCodePlus
                            (Maybe (Int, Int))
  deriving (Show)

-- FIXME: (WeakData, WeakDataMeta)としたほうがe : Aに揃って読みやすいかもしれない。
type WeakDataPlus = (WeakDataMeta, WeakData)

type WeakCodePlus = (WeakCodeMeta, WeakCode)

obtainInfoWeakCodeMeta :: WeakCodeMeta -> (WeakCodePlus, Maybe (Int, Int))
obtainInfoWeakCodeMeta (WeakCodeMetaTerminal ml) =
  ((WeakCodeMetaTerminal ml, WeakCodeTau), ml)
obtainInfoWeakCodeMeta (WeakCodeMetaNonTerminal t ml) = (t, ml)

obtainInfoWeakDataMeta :: WeakDataMeta -> (WeakDataPlus, Maybe (Int, Int))
obtainInfoWeakDataMeta (WeakDataMetaTerminal ml) =
  ((WeakDataMetaTerminal ml, WeakDataTau), ml)
obtainInfoWeakDataMeta (WeakDataMetaNonTerminal t ml) = (t, ml)

varWeakDataPlus :: WeakDataPlus -> [IdentifierPlus]
varWeakDataPlus (_, WeakDataTau) = []
varWeakDataPlus (m, WeakDataUpsilon x) = [(x, fst $ obtainInfoWeakDataMeta m)]
varWeakDataPlus (_, WeakDataEpsilon _) = []
varWeakDataPlus (_, WeakDataEpsilonIntro _) = []
varWeakDataPlus (_, WeakDataDownIntroPiIntro xps e) =
  filterPlus (`notElem` map fst xps) $
  concatMap (varWeakDataPlus . snd) xps ++ varWeakCodePlus e
varWeakDataPlus (_, WeakDataSigma xps p) =
  varWeakDataPlusPiOrSigma xps (varWeakDataPlus p)
varWeakDataPlus (_, WeakDataSigmaIntro vs) = concatMap varWeakDataPlus vs
varWeakDataPlus (_, WeakDataDown n) = varWeakCodePlus n

varWeakDataPlusPiOrSigma ::
     [IdentifierPlus] -> [IdentifierPlus] -> [IdentifierPlus]
varWeakDataPlusPiOrSigma [] xs = xs
varWeakDataPlusPiOrSigma ((x, p):xps) xs =
  varWeakDataPlus p ++ filterPlus (/= x) (varWeakDataPlusPiOrSigma xps xs)

varWeakCodePlus :: WeakCodePlus -> [IdentifierPlus]
varWeakCodePlus (_, WeakCodeTau) = []
varWeakCodePlus (_, WeakCodeTheta e) = varWeakTheta e
varWeakCodePlus (_, WeakCodeEpsilonElim (x, _) v branchList) = do
  let (_, es) = unzip branchList
  varWeakDataPlus v ++ filterPlus (/= x) (concatMap varWeakCodePlus es)
varWeakCodePlus (_, WeakCodePi xps n) =
  varWeakDataPlusPiOrSigma xps (varWeakCodePlus n)
varWeakCodePlus (_, WeakCodePiElimDownElim v vs) =
  varWeakDataPlus v ++ concatMap varWeakDataPlus vs
varWeakCodePlus (_, WeakCodeSigmaElim xps v e) =
  varWeakDataPlus v ++ filterPlus (`notElem` map fst xps) (varWeakCodePlus e)
varWeakCodePlus (_, WeakCodeUp p) = varWeakDataPlus p
varWeakCodePlus (_, WeakCodeUpIntro v) = varWeakDataPlus v
varWeakCodePlus (_, WeakCodeUpElim (x, _) e1 e2) =
  varWeakCodePlus e1 ++ filterPlus (/= x) (varWeakCodePlus e2)
varWeakCodePlus (_, WeakCodeMu (x, _) e) = filterPlus (/= x) $ varWeakCodePlus e

varWeakDataPlusPi :: [IdentifierPlus] -> WeakDataPlus -> [IdentifierPlus]
varWeakDataPlusPi [] n = varWeakDataPlus n
varWeakDataPlusPi ((x, p):xps) n =
  varWeakDataPlus p ++ filterPlus (/= x) (varWeakDataPlusPi xps n)

varWeakTheta :: WeakTheta -> [IdentifierPlus]
varWeakTheta = undefined

filterPlus :: (Identifier -> Bool) -> [IdentifierPlus] -> [IdentifierPlus]
filterPlus = undefined

type SubstWeakDataPlus = [IdentifierPlus]

substWeakDataPlus :: SubstWeakDataPlus -> WeakDataPlus -> WeakDataPlus
substWeakDataPlus sub (m, WeakDataTau) = do
  let m' = substWeakDataMeta sub m
  (m', WeakDataTau)
substWeakDataPlus sub (m, WeakDataUpsilon s) = do
  let m' = substWeakDataMeta sub m
  fromMaybe (m', WeakDataUpsilon s) (lookup s sub)
substWeakDataPlus sub (m, WeakDataEpsilon k) = do
  let m' = substWeakDataMeta sub m
  (m', WeakDataEpsilon k)
substWeakDataPlus sub (m, WeakDataEpsilonIntro l) = do
  let m' = substWeakDataMeta sub m
  (m', WeakDataEpsilonIntro l)
substWeakDataPlus sub (m, WeakDataDownIntroPiIntro xps e) = do
  let (xps', e') = substWeakCodePlusPi sub xps e
  let m' = substWeakDataMeta sub m
  (m', WeakDataDownIntroPiIntro xps' e')
substWeakDataPlus sub (m, WeakDataSigma xps p) = do
  let (xps', p') = substWeakDataPlusSigma sub xps p
  let m' = substWeakDataMeta sub m
  (m', WeakDataSigma xps' p')
substWeakDataPlus sub (m, WeakDataSigmaIntro vs) = do
  let vs' = map (substWeakDataPlus sub) vs
  let m' = substWeakDataMeta sub m
  (m', WeakDataSigmaIntro vs')
substWeakDataPlus sub (m, WeakDataDown n) = do
  let n' = substWeakCodePlus sub n
  let m' = substWeakDataMeta sub m
  (m', WeakDataDown n')

substWeakDataMeta :: SubstWeakDataPlus -> WeakDataMeta -> WeakDataMeta
substWeakDataMeta _ (WeakDataMetaTerminal ml) = WeakDataMetaTerminal ml
substWeakDataMeta sub (WeakDataMetaNonTerminal p ml) =
  WeakDataMetaNonTerminal (substWeakDataPlus sub p) ml

substWeakCodeMeta :: SubstWeakDataPlus -> WeakCodeMeta -> WeakCodeMeta
substWeakCodeMeta _ (WeakCodeMetaTerminal ml) = WeakCodeMetaTerminal ml
substWeakCodeMeta sub (WeakCodeMetaNonTerminal p ml) =
  WeakCodeMetaNonTerminal (substWeakCodePlus sub p) ml

substWeakCodePlus :: SubstWeakDataPlus -> WeakCodePlus -> WeakCodePlus
substWeakCodePlus sub (m, WeakCodeTau) = do
  let m' = substWeakCodeMeta sub m
  (m', WeakCodeTau)
substWeakCodePlus sub (m, WeakCodeTheta theta) = do
  let m' = substWeakCodeMeta sub m
  let theta' = substWeakTheta sub theta
  (m', WeakCodeTheta theta')
substWeakCodePlus sub (m, WeakCodeEpsilonElim (x, p) v branchList) = do
  let p' = substWeakDataPlus sub p
  let v' = substWeakDataPlus sub v
  let (cs, es) = unzip branchList
  let es' = map (substWeakCodePlus (filter (\(y, _) -> y /= x) sub)) es
  let branchList' = zip cs es'
  let m' = substWeakCodeMeta sub m
  (m', WeakCodeEpsilonElim (x, p') v' branchList')
substWeakCodePlus sub (m, WeakCodePi xps n) = do
  let (xps', n') = substWeakDataPlusPi sub xps n
  let m' = substWeakCodeMeta sub m
  (m', WeakCodePi xps' n')
substWeakCodePlus sub (m, WeakCodePiElimDownElim v vs) = do
  let v' = substWeakDataPlus sub v
  let vs' = map (substWeakDataPlus sub) vs
  let m' = substWeakCodeMeta sub m
  (m', WeakCodePiElimDownElim v' vs')
substWeakCodePlus sub (m, WeakCodeSigmaElim xps v e) = do
  let v' = substWeakDataPlus sub v
  let (xps', e') = substWeakDataPlusSigmaElim sub xps e
  let m' = substWeakCodeMeta sub m
  (m', WeakCodeSigmaElim xps' v' e')
substWeakCodePlus sub (m, WeakCodeUp p) = do
  let p' = substWeakDataPlus sub p
  let m' = substWeakCodeMeta sub m
  (m', WeakCodeUp p')
substWeakCodePlus sub (m, WeakCodeUpIntro v) = do
  let v' = substWeakDataPlus sub v
  let m' = substWeakCodeMeta sub m
  (m', WeakCodeUpIntro v')
substWeakCodePlus sub (m, WeakCodeUpElim (x, p) e1 e2) = do
  let p' = substWeakDataPlus sub p
  let e1' = substWeakCodePlus sub e1
  let e2' = substWeakCodePlus (filter (\(y, _) -> y /= x) sub) e2
  let m' = substWeakCodeMeta sub m
  (m', WeakCodeUpElim (x, p') e1' e2')
substWeakCodePlus sub (m, WeakCodeMu (x, p) e) = do
  let p' = substWeakDataPlus sub p
  let e' = substWeakCodePlus (filter (\(y, _) -> y /= x) sub) e
  let m' = substWeakCodeMeta sub m
  (m', WeakCodeMu (x, p') e')

substWeakTheta :: SubstWeakDataPlus -> WeakTheta -> WeakTheta
substWeakTheta sub (WeakThetaArith a v1 v2) = do
  let v1' = substWeakDataPlus sub v1
  let v2' = substWeakDataPlus sub v2
  WeakThetaArith a v1' v2'
substWeakTheta sub (WeakThetaPrint v) = WeakThetaPrint $ substWeakDataPlus sub v

substWeakDataPlusPiOrSigma ::
     SubstWeakDataPlus -> [IdentifierPlus] -> [IdentifierPlus]
substWeakDataPlusPiOrSigma _ [] = []
substWeakDataPlusPiOrSigma sub ((x, p):xps) = do
  let xps' = substWeakDataPlusPiOrSigma (filter (\(y, _) -> y /= x) sub) xps
  let p' = substWeakDataPlus sub p
  (x, p') : xps'

substWeakDataPlusPi ::
     SubstWeakDataPlus
  -> [IdentifierPlus]
  -> WeakCodePlus
  -> ([IdentifierPlus], WeakCodePlus)
substWeakDataPlusPi sub [] n = ([], substWeakCodePlus sub n)
substWeakDataPlusPi sub ((x, p):xps) n = do
  let (xps', n') = substWeakDataPlusPi (filter (\(y, _) -> y /= x) sub) xps n
  ((x, substWeakDataPlus sub p) : xps', n')

substWeakDataPlusSigma ::
     SubstWeakDataPlus
  -> [IdentifierPlus]
  -> WeakDataPlus
  -> ([IdentifierPlus], WeakDataPlus)
substWeakDataPlusSigma sub [] q = ([], substWeakDataPlus sub q)
substWeakDataPlusSigma sub ((x, p):xps) q = do
  let (xps', q') = substWeakDataPlusSigma (filter (\(y, _) -> y /= x) sub) xps q
  ((x, substWeakDataPlus sub p) : xps', q')

substWeakCodePlusPi ::
     SubstWeakDataPlus
  -> [IdentifierPlus]
  -> WeakCodePlus
  -> ([IdentifierPlus], WeakCodePlus)
substWeakCodePlusPi sub [] n = ([], substWeakCodePlus sub n)
substWeakCodePlusPi sub ((x, p):xps) n = do
  let (xps', n') = substWeakCodePlusPi (filter (\(y, _) -> y /= x) sub) xps n
  let p' = substWeakDataPlus sub p
  ((x, p') : xps', n')

substWeakDataPlusSigmaElim ::
     SubstWeakDataPlus
  -> [IdentifierPlus]
  -> WeakCodePlus
  -> ([IdentifierPlus], WeakCodePlus)
substWeakDataPlusSigmaElim sub [] e = do
  let e' = substWeakCodePlus sub e
  ([], e')
substWeakDataPlusSigmaElim sub ((x, p):xps) e = do
  let sub' = filter (\(y, _) -> y /= x) sub
  let (xps', e') = substWeakDataPlusSigmaElim sub' xps e
  let p' = substWeakDataPlus sub p
  ((x, p') : xps', e')
