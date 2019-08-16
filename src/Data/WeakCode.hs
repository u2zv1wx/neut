module Data.WeakCode where

import           Control.Monad (forM)
import           Data.Maybe    (fromMaybe)

import           Data.Basic

data WeakData
  = WeakDataTau
  | WeakDataTheta Identifier
  | WeakDataUpsilon Identifier
  | WeakDataEpsilon Identifier
  | WeakDataEpsilonIntro Literal
  | WeakDataSigma [IdentifierPlus]
                  WeakDataPlus
  | WeakDataSigmaIntro [WeakDataPlus]
                       WeakDataPlus
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
                      IdentifierPlus
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
  = WeakDataMetaTerminal (Maybe (Int, Int))
  | WeakDataMetaNonTerminal WeakDataPlus
                            (Maybe (Int, Int))
  deriving (Show)

data WeakCodeMeta =
  WeakCodeMetaNonTerminal WeakCodePlus
                          (Maybe (Int, Int))
  deriving (Show)

type WeakDataPlus = (WeakDataMeta, WeakData)

type WeakCodePlus = (WeakCodeMeta, WeakCode)

varWeakData :: WeakDataPlus -> [Identifier]
varWeakData (_, WeakDataTau) = []
varWeakData (_, WeakDataTheta _) = []
varWeakData (_, WeakDataUpsilon x) = [x]
varWeakData (_, WeakDataEpsilon _) = []
varWeakData (_, WeakDataEpsilonIntro _) = []
varWeakData (_, WeakDataSigma xts t) = undefined
varWeakData (_, WeakDataSigmaIntro es e) =
  varWeakData e ++ concatMap varWeakData es
varWeakData (_, WeakDataDown e) = undefined
varWeakData (_, WeakDataDownIntro e) = undefined

varWeakCode :: WeakCodePlus -> [Identifier]
varWeakCode (_, WeakCodeEpsilonElim (x, t) e branchList) = do
  let xhs1 = varWeakData t
  let xhs2 = varWeakData e
  xhss <-
    forM branchList $ \(_, body) -> do
      let xs = varWeakCode body
      return (filter (/= x) xs)
  xhs1 ++ xhs2 ++ concat xhss
varWeakCode (_, WeakCodePi xts t) = undefined
varWeakCode (_, WeakCodePiIntro xts e) = undefined
varWeakCode (_, WeakCodePiElim e es) = undefined
varWeakCode (_, WeakCodeSigmaElim xts xt e1 e2) = undefined
varWeakCode (_, WeakCodeMu ut e) = undefined
varWeakCode (_, WeakCodeUp _) = undefined
varWeakCode (_, WeakCodeUpIntro _) = undefined
varWeakCode (_, WeakCodeUpElim _ _ _) = undefined
varWeakCode (_, WeakCodeDownElim _) = undefined
-- substWeakData :: SubstWeakData -> WeakData -> WeakData
-- substWeakData sub (WeakDataUpsilon s) = fromMaybe (WeakDataUpsilon s) (lookup s sub)
-- substWeakData _ (WeakDataConst s) = WeakDataConst s
-- substWeakData sub (WeakDataSigmaIntro vs) = do
--   let vs' = map (substWeakData sub) vs
--   WeakDataSigmaIntro vs'
-- substWeakData _ (WeakDataEpsilonIntro l t) = WeakDataEpsilonIntro l t
-- substWeakCode :: SubstWeakData -> WeakCode -> WeakCode
-- substWeakCode sub (WeakCodePiElimDownElim v vs) = do
--   let v1' = substWeakData sub v
--   let v2' = map (substWeakData sub) vs
--   WeakCodePiElimDownElim v1' v2'
-- substWeakCode sub (WeakCodeSigmaElim xs v e) = do
--   let v' = substWeakData sub v
--   let sub' = filter (\(x, _) -> x `notElem` xs) sub
--   let e' = substWeakCode sub' e
--   WeakCodeSigmaElim xs v' e'
-- substWeakCode sub (WeakCodeEpsilonElim v branchList) = do
--   let v' = substWeakData sub v
--   let branchList' = map (\(l, e) -> (l, substWeakCode sub e)) branchList
--   WeakCodeEpsilonElim v' branchList'
-- substWeakCode sub (WeakCodeUpIntro v) = WeakCodeUpIntro $ substWeakData sub v
-- substWeakCode sub (WeakCodeUpElim x e1 e2) = do
--   let e1' = substWeakCode sub e1
--   let sub' = filter (\(y, _) -> x /= y) sub
--   let e2' = substWeakCode sub' e2
--   WeakCodeUpElim x e1' e2'
-- substWeakCode sub (WeakCodeConstElim x vs) = WeakCodeConstElim x $ map (substWeakData sub) vs
