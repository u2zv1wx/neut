module Data.Term where

import Control.Monad (forM)
import Data.List (nubBy)
import Data.Maybe (fromMaybe)

import Data.Basic

data Term
  = TermTau
  | TermTheta Identifier
  | TermUpsilon Identifier
  | TermEpsilon Identifier
  | TermEpsilonIntro Literal LowType
  | TermEpsilonElim IdentifierPlus TermPlus [(Case, TermPlus)]
  | TermPi [IdentifierPlus]
  | TermPiIntro [IdentifierPlus] TermPlus
  | TermPiElim TermPlus [TermPlus]
  | TermMu (Identifier, TermPlus) TermPlus
  deriving (Show)

data Meta
  = MetaTerminal (Maybe Loc)
  | MetaNonTerminal TermPlus (Maybe Loc)
  deriving (Show)

type TermPlus = (Meta, Term)

type SubstTerm = [(Identifier, TermPlus)]

type Hole = Identifier

type IdentifierPlus = (Identifier, TermPlus)

obtainInfoMeta :: Meta -> (TermPlus, Maybe Loc)
obtainInfoMeta (MetaTerminal ml) = ((MetaTerminal ml, TermTau), ml)
obtainInfoMeta (MetaNonTerminal t ml) = (t, ml)

toTermUpsilon :: (Identifier, TermPlus) -> TermPlus
toTermUpsilon (x, t) = do
  let (_, ml) = obtainInfoMeta $ fst t
  (MetaNonTerminal t ml, TermUpsilon x)

varTermPlus :: TermPlus -> [(Identifier, Maybe Loc, TermPlus)]
varTermPlus e = nubBy (\(x, _, _) (y, _, _) -> x == y) $ getClosedVarChain e

getClosedVarChain :: TermPlus -> [(Identifier, Maybe Loc, TermPlus)]
getClosedVarChain (_, TermTau) = []
getClosedVarChain (_, TermTheta _) = []
getClosedVarChain (m, TermUpsilon x) =
  case m of
    MetaTerminal ml -> [(x, ml, (m, TermTau))]
    MetaNonTerminal t ml -> getClosedVarChain t ++ [(x, ml, t)]
getClosedVarChain (_, TermEpsilon _) = []
getClosedVarChain (_, TermEpsilonIntro _ _) = []
getClosedVarChain (_, TermEpsilonElim (x, t) e branchList) = do
  let xhs1 = getClosedVarChain t
  let xhs2 = getClosedVarChain e
  xhss <-
    forM branchList $ \(_, body) -> do
      let xs = getClosedVarChain body
      return (filter (\(y, _, _) -> y /= x) xs)
  concat (xhs1 : xhs2 : xhss)
getClosedVarChain (_, TermPi xts) = getClosedVarChainBindings xts []
getClosedVarChain (_, TermPiIntro xts e) = getClosedVarChainBindings xts [e]
getClosedVarChain (_, TermPiElim e es) =
  getClosedVarChain e ++ concatMap getClosedVarChain es
getClosedVarChain (_, TermMu ut e) = getClosedVarChainBindings [ut] [e]

getClosedVarChainBindings ::
     [(Identifier, TermPlus)]
  -> [TermPlus]
  -> [(Identifier, Maybe Loc, TermPlus)]
getClosedVarChainBindings [] es = concatMap getClosedVarChain es
getClosedVarChainBindings ((x, t):xts) es = do
  let xs1 = getClosedVarChain t
  let xs2 = getClosedVarChainBindings xts es
  xs1 ++ filter (\(y, _, _) -> y /= x) xs2

substTermPlus :: SubstTerm -> TermPlus -> TermPlus
substTermPlus _ (m, TermTau) = (m, TermTau)
substTermPlus _ (m, TermTheta t) = (m, TermTheta t)
substTermPlus sub (m, TermUpsilon x) =
  fromMaybe (m, TermUpsilon x) (lookup x sub)
substTermPlus _ (m, TermEpsilon x) = (m, TermEpsilon x)
substTermPlus _ (m, TermEpsilonIntro l lowType) =
  (m, TermEpsilonIntro l lowType)
substTermPlus sub (m, TermEpsilonElim (x, t) e branchList) = do
  let t' = substTermPlus sub t
  let e' = substTermPlus sub e
  let (caseList, es) = unzip branchList
  let sub' = filter (\(k, _) -> k /= x) sub
  let es' = map (substTermPlus sub') es
  (m, TermEpsilonElim (x, t') e' (zip caseList es'))
substTermPlus sub (m, TermPi xts) = do
  let xts' = substTermPlusBindings sub xts
  (m, TermPi xts')
substTermPlus sub (m, TermPiIntro xts body) = do
  let (xts', body') = substTermPlusBindingsWithBody sub xts body
  (m, TermPiIntro xts' body')
substTermPlus sub (m, TermPiElim e es) = do
  let e' = substTermPlus sub e
  let es' = map (substTermPlus sub) es
  (m, TermPiElim e' es')
substTermPlus sub (m, TermMu (x, t) e) = do
  let t' = substTermPlus sub t
  let e' = substTermPlus (filter (\(k, _) -> k /= x) sub) e
  (m, TermMu (x, t') e')

substTermPlusBindings :: SubstTerm -> [IdentifierPlus] -> [IdentifierPlus]
substTermPlusBindings _ [] = []
substTermPlusBindings sub ((x, t):xts) = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let xts' = substTermPlusBindings sub' xts
  (x, substTermPlus sub t) : xts'

substTermPlusBindingsWithBody ::
     SubstTerm -> [IdentifierPlus] -> TermPlus -> ([IdentifierPlus], TermPlus)
substTermPlusBindingsWithBody sub [] e = ([], substTermPlus sub e)
substTermPlusBindingsWithBody sub ((x, t):xts) e = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let (xts', e') = substTermPlusBindingsWithBody sub' xts e
  ((x, substTermPlus sub t) : xts', e')

isValue :: TermPlus -> Bool
isValue (_, TermTau) = True
isValue (_, TermUpsilon _) = True
isValue (_, TermEpsilon _) = True
isValue (_, TermEpsilonIntro _ _) = True
isValue (_, TermPi {}) = True
isValue (_, TermPiIntro {}) = True
isValue _ = False
