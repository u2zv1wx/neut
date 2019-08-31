module Data.Term where

import           Control.Monad (forM)
import           Data.Maybe    (fromMaybe)

import           Data.Basic

data Term
  = TermTau
  | TermTheta Identifier
  | TermUpsilon Identifier
  | TermEpsilon Identifier
  | TermEpsilonIntro Literal
  | TermEpsilonElim IdentifierPlus
                    TermPlus
                    [(Case, TermPlus)]
  | TermPi [IdentifierPlus]
           TermPlus
  | TermPiIntro [IdentifierPlus]
                TermPlus
  | TermPiElim TermPlus
               [TermPlus]
  | TermMu (Identifier, TermPlus)
           TermPlus
  deriving (Show)

data Meta
  = MetaTerminal (Maybe Loc)
  | MetaNonTerminal TermPlus
                    (Maybe Loc)
  deriving (Show)

type TermPlus = (Meta, Term)

type SubstTerm = [(Identifier, TermPlus)]

type Hole = Identifier

type IdentifierPlus = (Identifier, TermPlus)

obtainInfoMeta :: Meta -> (TermPlus, Maybe Loc)
obtainInfoMeta (MetaTerminal ml)      = ((MetaTerminal ml, TermTau), ml)
obtainInfoMeta (MetaNonTerminal t ml) = (t, ml)

toTermUpsilon :: (Identifier, TermPlus) -> TermPlus
toTermUpsilon (x, t) = do
  let (_, ml) = obtainInfoMeta $ fst t
  (MetaNonTerminal t ml, TermUpsilon x)

varTermPlus :: TermPlus -> [IdentifierPlus]
varTermPlus (_, TermTau) = []
varTermPlus (_, TermTheta _) = []
varTermPlus (m, TermUpsilon x) = [(x, fst $ obtainInfoMeta m)]
varTermPlus (_, TermEpsilon _) = []
varTermPlus (_, TermEpsilonIntro _) = []
varTermPlus (_, TermEpsilonElim (x, t) e branchList) = do
  let xhs1 = varTermPlus t
  let xhs2 = varTermPlus e
  xhss <-
    forM branchList $ \(_, body) -> do
      let xs = varTermPlus body
      return (filter (\(y, _) -> y /= x) xs)
  concat (xhs1 : xhs2 : xhss)
varTermPlus (_, TermPi xts t) = varTermPlusBindings xts [] ++ varTermPlus t
varTermPlus (_, TermPiIntro xts e) = varTermPlusBindings xts [e]
varTermPlus (_, TermPiElim e es) = varTermPlus e ++ concatMap varTermPlus es
varTermPlus (_, TermMu ut e) = varTermPlusBindings [ut] [e]

varTermPlusBindings :: [IdentifierPlus] -> [TermPlus] -> [IdentifierPlus]
varTermPlusBindings [] es = concatMap varTermPlus es
varTermPlusBindings ((x, t):xts) es = do
  let xs1 = varTermPlus t
  let xs2 = varTermPlusBindings xts es
  xs1 ++ filter (\(y, _) -> y /= x) xs2

pairwiseConcat :: [([a], [b])] -> ([a], [b])
pairwiseConcat [] = ([], [])
pairwiseConcat ((xs, ys):rest) = do
  let (xs', ys') = pairwiseConcat rest
  (xs ++ xs', ys ++ ys')

substTermPlus :: SubstTerm -> TermPlus -> TermPlus
substTermPlus _ (m, TermTau) = (m, TermTau)
substTermPlus _ (m, TermTheta t) = (m, TermTheta t)
substTermPlus sub (m, TermUpsilon x) =
  fromMaybe (m, TermUpsilon x) (lookup x sub)
substTermPlus _ (m, TermEpsilon x) = (m, TermEpsilon x)
substTermPlus _ (m, TermEpsilonIntro l) = (m, TermEpsilonIntro l)
substTermPlus sub (m, TermEpsilonElim (x, t) e branchList) = do
  let t' = substTermPlus sub t
  let e' = substTermPlus sub e
  let (caseList, es) = unzip branchList
  let sub' = filter (\(k, _) -> k /= x) sub
  let es' = map (substTermPlus sub') es
  (m, TermEpsilonElim (x, t') e' (zip caseList es'))
substTermPlus sub (m, TermPi xts t) = do
  let xts' = substTermPlusBindings sub xts
  let t' = substTermPlus (filter (\(k, _) -> k `notElem` map fst xts) sub) t
  (m, TermPi xts' t')
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

isReducible :: TermPlus -> Bool
isReducible (_, TermTau) = False
isReducible (_, TermTheta _) = False
isReducible (_, TermUpsilon _) = False
isReducible (_, TermEpsilon _) = False
isReducible (_, TermEpsilonIntro _) = False
isReducible (_, TermEpsilonElim _ (_, TermEpsilonIntro l) branchList) = do
  let (caseList, _) = unzip branchList
  CaseLiteral l `elem` caseList || CaseDefault `elem` caseList
isReducible (_, TermEpsilonElim (_, _) e _) = isReducible e
isReducible (_, TermPi _ _) = False
isReducible (_, TermPiIntro {}) = False
isReducible (_, TermPiElim (_, TermPiIntro xts _) es)
  | length xts == length es = True
isReducible (_, TermPiElim (_, TermMu _ _) _) = True -- CBV recursion
isReducible (_, TermPiElim (_, TermTheta c) [(_, TermEpsilonIntro (LiteralInteger _)), (_, TermEpsilonIntro (LiteralInteger _))]) -- constant application
  | c `elem` intArithConstantList = True
isReducible (_, TermPiElim e es) = isReducible e || any isReducible es
isReducible (_, TermMu _ _) = False

isPure :: TermPlus -> Bool
isPure (_, TermTau) = True
isPure (_, TermTheta theta) = isPureConstant theta
isPure (_, TermUpsilon _) = True
isPure (_, TermEpsilon _) = True
isPure (_, TermEpsilonIntro _) = True
isPure (_, TermEpsilonElim _ (_, TermEpsilonIntro l) branchList) = do
  let (caseList, _) = unzip branchList
  CaseLiteral l `elem` caseList || CaseDefault `elem` caseList
isPure (_, TermEpsilonElim (_, _) e _) = isPure e
isPure (_, TermPi _ _) = True
isPure (_, TermPiIntro {}) = True
isPure (_, TermPiElim e es) = isPure e || all isPure es
isPure (_, TermMu _ _) = True

isPureConstant :: Identifier -> Bool
isPureConstant = undefined

isValue :: TermPlus -> Bool
isValue (_, TermTau)            = True
isValue (_, TermUpsilon _)      = True
isValue (_, TermEpsilon _)      = True
isValue (_, TermEpsilonIntro _) = True
isValue (_, TermPi {})          = True
isValue (_, TermPiIntro {})     = True
isValue _                       = False
