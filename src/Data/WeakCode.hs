module Data.WeakCode where

import           Data.Maybe (fromMaybe)

import           Data.Basic

data WeakData
  = WeakDataTau
  | WeakDataTheta Identifier
  | WeakDataUpsilon Identifier
  | WeakDataEpsilon Identifier
  | WeakDataEpsilonIntro Literal
  | WeakDataPi [IdentifierPlus]
  | WeakDataSigma [IdentifierPlus]
  | WeakDataSigmaIntro [WeakDataPlus]
  | WeakDataUp WeakDataPlus
  | WeakDataDown WeakDataPlus
  | WeakDataDownIntro WeakCodePlus
  deriving (Show)

data WeakCode
  = WeakCodeEpsilonElim IdentifierPlus
                        WeakDataPlus
                        [(Case, WeakCodePlus)]
  | WeakCodePiIntro [IdentifierPlus]
                    WeakCodePlus
  | WeakCodePiElim WeakCodePlus
                   [WeakDataPlus]
  | WeakCodeSigmaElim [IdentifierPlus]
                      WeakDataPlus
                      WeakCodePlus
  | WeakCodeUpIntro WeakDataPlus
  | WeakCodeUpElim IdentifierPlus
                   WeakCodePlus
                   WeakCodePlus
  | WeakCodeDownElim WeakDataPlus
  | WeakCodeMu IdentifierPlus
               WeakCodePlus
  deriving (Show)

type IdentifierPlus = (Identifier, WeakDataPlus)

data WeakMeta
  = WeakMetaTerminal (Maybe (Int, Int))
  | WeakMetaNonTerminal WeakDataPlus
                        (Maybe (Int, Int))
  deriving (Show)

-- FIXME: (WeakData, WeakDataMeta)としたほうがe : Aに揃って読みやすいかもしれない。
type WeakDataPlus = (WeakMeta, WeakData)

type WeakCodePlus = (WeakMeta, WeakCode)

varWeakDataPlus :: WeakDataPlus -> [Identifier]
varWeakDataPlus (_, WeakDataTau)            = []
varWeakDataPlus (_, WeakDataTheta _)        = []
varWeakDataPlus (_, WeakDataUpsilon x)      = [x]
varWeakDataPlus (_, WeakDataEpsilon _)      = []
varWeakDataPlus (_, WeakDataEpsilonIntro _) = []
varWeakDataPlus (_, WeakDataPi xps)         = varWeakDataPlusPiOrSigma xps
varWeakDataPlus (_, WeakDataSigma xps)      = varWeakDataPlusPiOrSigma xps
varWeakDataPlus (_, WeakDataSigmaIntro vs)  = concatMap varWeakDataPlus vs
varWeakDataPlus (_, WeakDataUp p)           = varWeakDataPlus p
varWeakDataPlus (_, WeakDataDown p)         = varWeakDataPlus p
varWeakDataPlus (_, WeakDataDownIntro e)    = varWeakCodePlus e

varWeakDataPlusPiOrSigma :: [IdentifierPlus] -> [Identifier]
varWeakDataPlusPiOrSigma [] = []
varWeakDataPlusPiOrSigma ((x, p):xps) =
  varWeakDataPlus p ++ filter (/= x) (varWeakDataPlusPiOrSigma xps)

varWeakCodePlus :: WeakCodePlus -> [Identifier]
varWeakCodePlus (_, WeakCodeEpsilonElim (x, _) v branchList) = do
  let (_, es) = unzip branchList
  varWeakDataPlus v ++ filter (/= x) (concatMap varWeakCodePlus es)
varWeakCodePlus (_, WeakCodePiIntro xps e) =
  filter (`notElem` map fst xps) $
  concatMap (varWeakDataPlus . snd) xps ++ varWeakCodePlus e
varWeakCodePlus (_, WeakCodePiElim e vs) =
  varWeakCodePlus e ++ concatMap varWeakDataPlus vs
varWeakCodePlus (_, WeakCodeSigmaElim xps v e) =
  varWeakDataPlus v ++ filter (`notElem` map fst xps) (varWeakCodePlus e)
varWeakCodePlus (_, WeakCodeUpIntro v) = varWeakDataPlus v
varWeakCodePlus (_, WeakCodeUpElim (x, _) e1 e2) =
  varWeakCodePlus e1 ++ filter (/= x) (varWeakCodePlus e2)
varWeakCodePlus (_, WeakCodeDownElim v) = varWeakDataPlus v
varWeakCodePlus (_, WeakCodeMu (x, _) e) = filter (/= x) $ varWeakCodePlus e

varWeakDataPlusPi :: [IdentifierPlus] -> WeakDataPlus -> [Identifier]
varWeakDataPlusPi [] n = varWeakDataPlus n
varWeakDataPlusPi ((x, p):xps) n =
  varWeakDataPlus p ++ filter (/= x) (varWeakDataPlusPi xps n)

type SubstWeakDataPlus = [IdentifierPlus]

substWeakDataPlus :: SubstWeakDataPlus -> WeakDataPlus -> WeakDataPlus
substWeakDataPlus sub (m, WeakDataTau) = do
  let m' = substWeakMeta sub m
  (m', WeakDataTau)
substWeakDataPlus sub (m, WeakDataUpsilon s) = do
  let m' = substWeakMeta sub m
  fromMaybe (m', WeakDataUpsilon s) (lookup s sub)
substWeakDataPlus sub (m, WeakDataTheta s) = do
  let m' = substWeakMeta sub m
  (m', WeakDataTheta s)
substWeakDataPlus sub (m, WeakDataEpsilon k) = do
  let m' = substWeakMeta sub m
  (m', WeakDataEpsilon k)
substWeakDataPlus sub (m, WeakDataEpsilonIntro l) = do
  let m' = substWeakMeta sub m
  (m', WeakDataEpsilonIntro l)
substWeakDataPlus sub (m, WeakDataPi xps) = do
  let xps' = substWeakDataPlusPiOrSigma sub xps
  let m' = substWeakMeta sub m
  (m', WeakDataPi xps')
substWeakDataPlus sub (m, WeakDataSigma xps) = do
  let xps' = substWeakDataPlusPiOrSigma sub xps
  let m' = substWeakMeta sub m
  (m', WeakDataSigma xps')
substWeakDataPlus sub (m, WeakDataSigmaIntro vs) = do
  let vs' = map (substWeakDataPlus sub) vs
  let m' = substWeakMeta sub m
  (m', WeakDataSigmaIntro vs')
substWeakDataPlus sub (m, WeakDataUp p) = do
  let p' = substWeakDataPlus sub p
  let m' = substWeakMeta sub m
  (m', WeakDataUp p')
substWeakDataPlus sub (m, WeakDataDown p) = do
  let p' = substWeakDataPlus sub p
  let m' = substWeakMeta sub m
  (m', WeakDataDown p')
substWeakDataPlus sub (m, WeakDataDownIntro e) = do
  let e' = substWeakCodePlus sub e
  let m' = substWeakMeta sub m
  (m', WeakDataDownIntro e')

substWeakMeta :: SubstWeakDataPlus -> WeakMeta -> WeakMeta
substWeakMeta _ (WeakMetaTerminal ml) = WeakMetaTerminal ml
substWeakMeta sub (WeakMetaNonTerminal p ml) =
  WeakMetaNonTerminal (substWeakDataPlus sub p) ml

substWeakCodePlus :: SubstWeakDataPlus -> WeakCodePlus -> WeakCodePlus
substWeakCodePlus sub (m, WeakCodeEpsilonElim (x, p) v branchList) = do
  let p' = substWeakDataPlus sub p
  let v' = substWeakDataPlus sub v
  let (cs, es) = unzip branchList
  let es' = map (substWeakCodePlus (filter (\(y, _) -> y /= x) sub)) es
  let branchList' = zip cs es'
  let m' = substWeakMeta sub m
  (m', WeakCodeEpsilonElim (x, p') v' branchList')
substWeakCodePlus sub (m, WeakCodePiIntro xps e) = do
  let (xps', e') = substWeakCodePlusPi sub xps e
  let m' = substWeakMeta sub m
  (m', WeakCodePiIntro xps' e')
substWeakCodePlus sub (m, WeakCodePiElim e vs) = do
  let e' = substWeakCodePlus sub e
  let vs' = map (substWeakDataPlus sub) vs
  let m' = substWeakMeta sub m
  (m', WeakCodePiElim e' vs')
substWeakCodePlus sub (m, WeakCodeSigmaElim xps v e) = do
  let v' = substWeakDataPlus sub v
  let (xps', e') = substWeakDataPlusSigmaElim sub xps e
  let m' = substWeakMeta sub m
  (m', WeakCodeSigmaElim xps' v' e')
substWeakCodePlus sub (m, WeakCodeUpIntro v) = do
  let v' = substWeakDataPlus sub v
  let m' = substWeakMeta sub m
  (m', WeakCodeUpIntro v')
substWeakCodePlus sub (m, WeakCodeUpElim (x, p) e1 e2) = do
  let p' = substWeakDataPlus sub p
  let e1' = substWeakCodePlus sub e1
  let e2' = substWeakCodePlus (filter (\(y, _) -> y /= x) sub) e2
  let m' = substWeakMeta sub m
  (m', WeakCodeUpElim (x, p') e1' e2')
substWeakCodePlus sub (m, WeakCodeDownElim v) = do
  let v' = substWeakDataPlus sub v
  let m' = substWeakMeta sub m
  (m', WeakCodeDownElim v')
substWeakCodePlus sub (m, WeakCodeMu (x, p) e) = do
  let p' = substWeakDataPlus sub p
  let e' = substWeakCodePlus (filter (\(y, _) -> y /= x) sub) e
  let m' = substWeakMeta sub m
  (m', WeakCodeMu (x, p') e')

substWeakDataPlusPiOrSigma ::
     SubstWeakDataPlus -> [IdentifierPlus] -> [IdentifierPlus]
substWeakDataPlusPiOrSigma _ [] = []
substWeakDataPlusPiOrSigma sub ((x, p):xps) = do
  let xps' = substWeakDataPlusPiOrSigma (filter (\(y, _) -> y /= x) sub) xps
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
