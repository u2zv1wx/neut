module Data.Term where

import Control.Monad (forM)
import Data.List (nubBy)
import Data.Maybe (fromMaybe)
import Numeric.Half

import Data.Basic

data Term
  = TermTau
  | TermTheta Identifier
  | TermUpsilon Identifier
  | TermEpsilon Identifier
  | TermEpsilonIntro Identifier LowType
  | TermEpsilonElim (Identifier, LowType) TermPlus [(Case, TermPlus)]
  | TermPi [IdentifierPlus]
  | TermPiIntro [IdentifierPlus] TermPlus
  | TermPiElim TermPlus [TermPlus]
  | TermMu (Identifier, TermPlus) TermPlus
  | TermInt Int LowType
  | TermFloat16 Half
  | TermFloat32 Float
  | TermFloat64 Double
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
getClosedVarChain (_, TermEpsilonElim (x, _) e branchList) = do
  let xhs = getClosedVarChain e
  xhss <-
    forM branchList $ \(_, body) -> do
      let xs = getClosedVarChain body
      return (filter (\(y, _, _) -> y /= x) xs)
  concat (xhs : xhss)
getClosedVarChain (_, TermPi xts) = getClosedVarChainBindings xts []
getClosedVarChain (_, TermPiIntro xts e) = getClosedVarChainBindings xts [e]
getClosedVarChain (_, TermPiElim e es) =
  getClosedVarChain e ++ concatMap getClosedVarChain es
getClosedVarChain (_, TermMu ut e) = getClosedVarChainBindings [ut] [e]
getClosedVarChain (_, TermInt _ _) = []
getClosedVarChain (_, TermFloat16 _) = []
getClosedVarChain (_, TermFloat32 _) = []
getClosedVarChain (_, TermFloat64 _) = []

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
substTermPlus sub (m, TermEpsilonElim (x, lowType) e branchList) = do
  let e' = substTermPlus sub e
  let (caseList, es) = unzip branchList
  let sub' = filter (\(k, _) -> k /= x) sub
  let es' = map (substTermPlus sub') es
  (m, TermEpsilonElim (x, lowType) e' (zip caseList es'))
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
substTermPlus _ (m, TermInt x lowType) = (m, TermInt x lowType)
substTermPlus _ (m, TermFloat16 x) = (m, TermFloat16 x)
substTermPlus _ (m, TermFloat32 x) = (m, TermFloat32 x)
substTermPlus _ (m, TermFloat64 x) = (m, TermFloat64 x)

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
