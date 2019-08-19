module Data.WeakCode where

import           Data.Maybe (fromMaybe)

import           Data.Basic

data WeakData
  = WeakDataTau
  | WeakDataTheta Identifier
  | WeakDataUpsilon Identifier
  | WeakDataEpsilon Identifier
  | WeakDataEpsilonIntro Literal
  | WeakDataSigma [IdentifierPlus]
  | WeakDataSigmaIntro [WeakDataPlus]
  | WeakDataDown WeakCodePlus
  | WeakDataDownIntro WeakCodePlus
  deriving (Show)

data WeakCode
  = WeakCodeEpsilonElim IdentifierPlus
                        WeakDataPlus
                        [(Case, WeakCodePlus)]
  | WeakCodePi [IdentifierPlus]
               WeakCodePlus
  | WeakCodePiIntro [IdentifierPlus]
                    WeakCodePlus
  | WeakCodePiElim WeakCodePlus
                   [WeakDataPlus]
  | WeakCodeSigmaElim [IdentifierPlus]
                      WeakDataPlus
                      WeakCodePlus
  | WeakCodeUp WeakDataPlus
  | WeakCodeUpIntro WeakDataPlus
  | WeakCodeUpElim IdentifierPlus
                   WeakCodePlus
                   WeakCodePlus
  | WeakCodeDownElim WeakDataPlus
  | WeakCodeMu IdentifierPlus
               WeakCodePlus
  deriving (Show)

type IdentifierPlus = (Identifier, WeakDataPlus)

data WeakDataMeta
  = WeakDataMetaTerminal (Maybe (Int, Int)) -- positive universe (univ+ : univ+)
  | WeakDataMetaNonTerminal WeakDataPlus
                            (Maybe (Int, Int))
  deriving (Show)

data WeakCodeMeta
  = WeakCodeMetaTerminal (Maybe (Int, Int)) -- negative universe (↑univ+ : univ-)
  | WeakCodeMetaNonTerminal WeakCodePlus
                            (Maybe (Int, Int))
  deriving (Show)

-- FIXME: (WeakData, WeakDataMeta)としたほうがe : Aに揃って読みやすいかもしれない。
type WeakDataPlus = (WeakDataMeta, WeakData)

type WeakCodePlus = (WeakCodeMeta, WeakCode)

varWeakDataPlus :: WeakDataPlus -> [Identifier]
varWeakDataPlus (_, WeakDataTau)            = []
varWeakDataPlus (_, WeakDataTheta _)        = []
varWeakDataPlus (_, WeakDataUpsilon x)      = [x]
varWeakDataPlus (_, WeakDataEpsilon _)      = []
varWeakDataPlus (_, WeakDataEpsilonIntro _) = []
varWeakDataPlus (_, WeakDataSigma xps)      = varWeakDataPlusSigma xps
varWeakDataPlus (_, WeakDataSigmaIntro vs)  = concatMap varWeakDataPlus vs
varWeakDataPlus (_, WeakDataDown n)         = varWeakCodePlus n
varWeakDataPlus (_, WeakDataDownIntro e)    = varWeakCodePlus e

varWeakDataPlusSigma :: [IdentifierPlus] -> [Identifier]
varWeakDataPlusSigma [] = []
varWeakDataPlusSigma ((x, p):xps) =
  varWeakDataPlus p ++ filter (/= x) (varWeakDataPlusSigma xps)

varWeakCodePlus :: WeakCodePlus -> [Identifier]
varWeakCodePlus (_, WeakCodeEpsilonElim (x, _) v branchList) = do
  let (_, es) = unzip branchList
  varWeakDataPlus v ++ filter (/= x) (concatMap varWeakCodePlus es)
varWeakCodePlus (_, WeakCodePi xps n) = varWeakCodePlusPi xps n
varWeakCodePlus (_, WeakCodePiIntro xps e) =
  filter (`notElem` map fst xps) $
  concatMap (varWeakDataPlus . snd) xps ++ varWeakCodePlus e
varWeakCodePlus (_, WeakCodePiElim e vs) =
  varWeakCodePlus e ++ concatMap varWeakDataPlus vs
varWeakCodePlus (_, WeakCodeSigmaElim xps v e) =
  varWeakDataPlus v ++ filter (`notElem` map fst xps) (varWeakCodePlus e)
varWeakCodePlus (_, WeakCodeUp p) = varWeakDataPlus p
varWeakCodePlus (_, WeakCodeUpIntro v) = varWeakDataPlus v
varWeakCodePlus (_, WeakCodeUpElim (x, _) e1 e2) =
  varWeakCodePlus e1 ++ filter (/= x) (varWeakCodePlus e2)
varWeakCodePlus (_, WeakCodeDownElim v) = varWeakDataPlus v
varWeakCodePlus (_, WeakCodeMu (x, _) e) = filter (/= x) $ varWeakCodePlus e

varWeakCodePlusPi :: [IdentifierPlus] -> WeakCodePlus -> [Identifier]
varWeakCodePlusPi [] n = varWeakCodePlus n
varWeakCodePlusPi ((x, p):xps) n =
  varWeakDataPlus p ++ filter (/= x) (varWeakCodePlusPi xps n)

type SubstWeakDataPlus = [IdentifierPlus]

substWeakDataPlus :: SubstWeakDataPlus -> WeakDataPlus -> WeakDataPlus
substWeakDataPlus sub (m, WeakDataTau) = do
  let m' = substWeakDataMeta sub m
  (m', WeakDataTau)
substWeakDataPlus sub (m, WeakDataUpsilon s) = do
  let m' = substWeakDataMeta sub m
  fromMaybe (m', WeakDataUpsilon s) (lookup s sub)
substWeakDataPlus sub (m, WeakDataTheta s) = do
  let m' = substWeakDataMeta sub m
  (m', WeakDataTheta s)
substWeakDataPlus sub (m, WeakDataEpsilon k) = do
  let m' = substWeakDataMeta sub m
  (m', WeakDataEpsilon k)
substWeakDataPlus sub (m, WeakDataEpsilonIntro l) = do
  let m' = substWeakDataMeta sub m
  (m', WeakDataEpsilonIntro l)
substWeakDataPlus sub (m, WeakDataSigma xps) = do
  let xps' = substWeakDataPlusSigma sub xps
  let m' = substWeakDataMeta sub m
  (m', WeakDataSigma xps')
substWeakDataPlus sub (m, WeakDataSigmaIntro vs) = do
  let vs' = map (substWeakDataPlus sub) vs
  let m' = substWeakDataMeta sub m
  (m', WeakDataSigmaIntro vs')
substWeakDataPlus sub (m, WeakDataDown n) = do
  let n' = substWeakCodePlus sub n
  let m' = substWeakDataMeta sub m
  (m', WeakDataDown n')
substWeakDataPlus sub (m, WeakDataDownIntro e) = do
  let e' = substWeakCodePlus sub e
  let m' = substWeakDataMeta sub m
  (m', WeakDataDownIntro e')

substWeakDataMeta :: SubstWeakDataPlus -> WeakDataMeta -> WeakDataMeta
substWeakDataMeta _ (WeakDataMetaTerminal ml) = WeakDataMetaTerminal ml
substWeakDataMeta sub (WeakDataMetaNonTerminal p ml) =
  WeakDataMetaNonTerminal (substWeakDataPlus sub p) ml

substWeakCodePlus :: SubstWeakDataPlus -> WeakCodePlus -> WeakCodePlus
substWeakCodePlus sub (m, WeakCodeEpsilonElim (x, p) v branchList) = do
  let p' = substWeakDataPlus sub p
  let v' = substWeakDataPlus sub v
  let (cs, es) = unzip branchList
  let es' = map (substWeakCodePlus (filter (\(y, _) -> y /= x) sub)) es
  let branchList' = zip cs es'
  let m' = substWeakCodeMeta sub m
  (m', WeakCodeEpsilonElim (x, p') v' branchList')
substWeakCodePlus sub (m, WeakCodePi xps n) = do
  let (xps', n') = substWeakCodePlusPi sub xps n
  let m' = substWeakCodeMeta sub m
  (m', WeakCodePi xps' n')
substWeakCodePlus sub (m, WeakCodePiIntro xps e) = do
  let (xps', e') = substWeakCodePlusPi sub xps e
  let m' = substWeakCodeMeta sub m
  (m', WeakCodePiIntro xps' e')
substWeakCodePlus sub (m, WeakCodePiElim e vs) = do
  let e' = substWeakCodePlus sub e
  let vs' = map (substWeakDataPlus sub) vs
  let m' = substWeakCodeMeta sub m
  (m', WeakCodePiElim e' vs')
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
substWeakCodePlus sub (m, WeakCodeDownElim v) = do
  let v' = substWeakDataPlus sub v
  let m' = substWeakCodeMeta sub m
  (m', WeakCodeDownElim v')
substWeakCodePlus sub (m, WeakCodeMu (x, p) e) = do
  let p' = substWeakDataPlus sub p
  let e' = substWeakCodePlus (filter (\(y, _) -> y /= x) sub) e
  let m' = substWeakCodeMeta sub m
  (m', WeakCodeMu (x, p') e')

substWeakCodeMeta :: SubstWeakDataPlus -> WeakCodeMeta -> WeakCodeMeta
substWeakCodeMeta _ (WeakCodeMetaTerminal ml) = WeakCodeMetaTerminal ml
substWeakCodeMeta sub (WeakCodeMetaNonTerminal n ml) =
  WeakCodeMetaNonTerminal (substWeakCodePlus sub n) ml

substWeakDataPlusSigma ::
     SubstWeakDataPlus -> [IdentifierPlus] -> [IdentifierPlus]
substWeakDataPlusSigma _ [] = []
substWeakDataPlusSigma sub ((x, p):xps) = do
  let xps' = substWeakDataPlusSigma (filter (\(y, _) -> y /= x) sub) xps
  let p' = substWeakDataPlus sub p
  (x, p') : xps'

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
