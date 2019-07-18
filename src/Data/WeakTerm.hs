{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

module Data.WeakTerm where

import           Control.Comonad.Cofree
import           Control.Monad          (forM)
import           Data.Maybe             (fromMaybe)
import           Text.Show.Deriving

import           Data.Basic

type IdentifierPlus = (Identifier, WeakTerm)

data WeakLevel
  = WeakLevelInt Int
  | WeakLevelInfinity
  | WeakLevelHole Identifier
  deriving (Show, Eq)

data WeakTermF a
  -- The "level" of WeakTermUniv is the one of modality, and thus not the one of
  -- universe hierarchy. We allow "univ : univ" since we've already allowed
  -- unlimited fixed point operator, which makes the system inconsistent as logic.
  = WeakTermUniv WeakLevel
  | WeakTermUpsilon Identifier
  | WeakTermEpsilon Identifier
  | WeakTermEpsilonIntro Literal
  | WeakTermEpsilonElim (Identifier, a)
                        a
                        [(Case, a)]
  | WeakTermPi [(Identifier, a)]
  | WeakTermPiIntro [(Identifier, a)]
                    a
  | WeakTermPiElim a
                   [a]
  | WeakTermSigma [(Identifier, a)]
  | WeakTermSigmaIntro [a]
  | WeakTermSigmaElim [(Identifier, a)]
                      a
                      a
  | WeakTermTau a -- K modality
  | WeakTermTauIntro a
  | WeakTermTauElim a
  | WeakTermTheta a -- S4 modality
  | WeakTermThetaIntro a
  | WeakTermThetaElim a
  | WeakTermMu (Identifier, a)
               a
  | WeakTermIota a -- level annotation
                 WeakLevel
  | WeakTermConst Identifier
  | WeakTermHole Identifier

type WeakTerm = Cofree WeakTermF Identifier

$(deriveShow1 ''WeakTermF)

type SubstWeakTerm = [(Identifier, WeakTerm)]

varWeakTerm :: WeakTerm -> [Identifier]
varWeakTerm e = fst $ varAndHole e

varAndHole :: WeakTerm -> ([Identifier], [Identifier])
varAndHole (_ :< WeakTermUniv _) = ([], [])
varAndHole (_ :< WeakTermUpsilon x) = ([x], [])
varAndHole (_ :< WeakTermEpsilon _) = ([], [])
varAndHole (_ :< WeakTermEpsilonIntro _) = ([], [])
varAndHole (_ :< WeakTermEpsilonElim (x, t) e branchList) = do
  let xhs1 = varAndHole t
  let xhs2 = varAndHole e
  xhss <-
    forM branchList $ \(_, body) -> do
      let (xs, hs) = varAndHole body
      return (filter (/= x) xs, hs)
  pairwiseConcat (xhs1 : xhs2 : xhss)
varAndHole (_ :< WeakTermPi xts) = varAndHoleBindings xts []
varAndHole (_ :< WeakTermPiIntro xts e) = varAndHoleBindings xts [e]
varAndHole (_ :< WeakTermPiElim e es) =
  pairwiseConcat $ varAndHole e : map varAndHole es
varAndHole (_ :< WeakTermSigma xts) = varAndHoleBindings xts []
varAndHole (_ :< WeakTermSigmaIntro es) = pairwiseConcat $ map varAndHole es
varAndHole (_ :< WeakTermSigmaElim us e1 e2) =
  pairwiseConcat [varAndHole e1, varAndHoleBindings us [e2]]
varAndHole (_ :< WeakTermTau t) = varAndHole t
varAndHole (_ :< WeakTermTauIntro e) = varAndHole e
varAndHole (_ :< WeakTermTauElim e) = varAndHole e
varAndHole (_ :< WeakTermTheta t) = varAndHole t
varAndHole (_ :< WeakTermThetaIntro e) = varAndHole e
varAndHole (_ :< WeakTermThetaElim e) = varAndHole e
varAndHole (_ :< WeakTermMu ut e) = varAndHoleBindings [ut] [e]
varAndHole (_ :< WeakTermIota e _) = varAndHole e
varAndHole (_ :< WeakTermConst _) = ([], [])
varAndHole (_ :< WeakTermHole x) = ([], [x])

varAndHoleBindings ::
     [IdentifierPlus] -> [WeakTerm] -> ([Identifier], [Identifier])
varAndHoleBindings [] es = pairwiseConcat $ map varAndHole es
varAndHoleBindings ((x, t):xts) es = do
  let (xs1, hs1) = varAndHole t
  let (xs2, hs2) = varAndHoleBindings xts es
  (xs1 ++ filter (/= x) xs2, hs1 ++ hs2)

pairwiseConcat :: [([a], [b])] -> ([a], [b])
pairwiseConcat [] = ([], [])
pairwiseConcat ((xs, ys):rest) = do
  let (xs', ys') = pairwiseConcat rest
  (xs ++ xs', ys ++ ys')

substWeakTerm :: SubstWeakTerm -> WeakTerm -> WeakTerm
substWeakTerm _ (j :< WeakTermUniv i) = j :< WeakTermUniv i
substWeakTerm sub (j :< WeakTermUpsilon x) =
  fromMaybe (j :< WeakTermUpsilon x) (lookup x sub)
substWeakTerm _ (j :< WeakTermEpsilon x) = j :< WeakTermEpsilon x
substWeakTerm _ (j :< WeakTermEpsilonIntro l) = j :< WeakTermEpsilonIntro l
substWeakTerm sub (j :< WeakTermEpsilonElim (x, t) e branchList) = do
  let t' = substWeakTerm sub t
  let e' = substWeakTerm sub e
  let (caseList, es) = unzip branchList
  let sub' = filter (\(k, _) -> k /= x) sub
  let es' = map (substWeakTerm sub') es
  j :< WeakTermEpsilonElim (x, t') e' (zip caseList es')
substWeakTerm sub (j :< WeakTermPi xts) = do
  let xts' = substWeakTermBindings sub xts
  j :< WeakTermPi xts'
substWeakTerm sub (j :< WeakTermPiIntro xts body) = do
  let (xts', body') = substWeakTermBindingsWithBody sub xts body
  j :< WeakTermPiIntro xts' body'
substWeakTerm sub (j :< WeakTermPiElim e es) = do
  let e' = substWeakTerm sub e
  let es' = map (substWeakTerm sub) es
  j :< WeakTermPiElim e' es'
substWeakTerm sub (j :< WeakTermSigma xts) = do
  let xts' = substWeakTermBindings sub xts
  j :< WeakTermSigma xts'
substWeakTerm sub (j :< WeakTermSigmaIntro es) = do
  let es' = map (substWeakTerm sub) es
  j :< WeakTermSigmaIntro es'
substWeakTerm sub (j :< WeakTermSigmaElim xts e1 e2) = do
  let e1' = substWeakTerm sub e1
  let (xts', e2') = substWeakTermBindingsWithBody sub xts e2
  j :< WeakTermSigmaElim xts' e1' e2'
substWeakTerm sub (j :< WeakTermTau t) = j :< WeakTermTau (substWeakTerm sub t)
substWeakTerm sub (j :< WeakTermTauIntro e) =
  j :< WeakTermTauIntro (substWeakTerm sub e)
substWeakTerm sub (j :< WeakTermTauElim e) =
  j :< WeakTermTauElim (substWeakTerm sub e)
substWeakTerm sub (j :< WeakTermTheta t) =
  j :< WeakTermTheta (substWeakTerm sub t)
substWeakTerm sub (j :< WeakTermThetaIntro e) =
  j :< WeakTermThetaIntro (substWeakTerm sub e)
substWeakTerm sub (j :< WeakTermThetaElim e) =
  j :< WeakTermThetaElim (substWeakTerm sub e)
substWeakTerm sub (j :< WeakTermMu (x, t) e) = do
  let t' = substWeakTerm sub t
  let e' = substWeakTerm (filter (\(k, _) -> k /= x) sub) e
  j :< WeakTermMu (x, t') e'
substWeakTerm sub (j :< WeakTermIota e i) =
  j :< WeakTermIota (substWeakTerm sub e) i
substWeakTerm _ (j :< WeakTermConst t) = j :< WeakTermConst t
substWeakTerm sub (j :< WeakTermHole s) =
  fromMaybe (j :< WeakTermHole s) (lookup s sub)

substWeakTermBindings :: SubstWeakTerm -> [IdentifierPlus] -> [IdentifierPlus]
substWeakTermBindings _ [] = []
substWeakTermBindings sub ((x, t):xts) = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let xts' = substWeakTermBindings sub' xts
  (x, substWeakTerm sub t) : xts'

substWeakTermBindingsWithBody ::
     SubstWeakTerm
  -> [IdentifierPlus]
  -> WeakTerm
  -> ([IdentifierPlus], WeakTerm)
substWeakTermBindingsWithBody sub [] e = ([], substWeakTerm sub e)
substWeakTermBindingsWithBody sub ((x, t):xts) e = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let (xts', e') = substWeakTermBindingsWithBody sub' xts e
  ((x, substWeakTerm sub t) : xts', e')

type SubstWeakLevel = [(Identifier, WeakLevel)]

substWeakLevel :: SubstWeakLevel -> WeakLevel -> WeakLevel
substWeakLevel _ (WeakLevelInt i) = WeakLevelInt i
substWeakLevel _ WeakLevelInfinity = WeakLevelInfinity
substWeakLevel sub (WeakLevelHole h) =
  fromMaybe (WeakLevelHole h) (lookup h sub)

isReducible :: WeakTerm -> Bool
isReducible (_ :< WeakTermUniv _) = False
isReducible (_ :< WeakTermUpsilon _) = False
isReducible (_ :< WeakTermEpsilon _) = False
isReducible (_ :< WeakTermEpsilonIntro _) = False
isReducible (_ :< WeakTermEpsilonElim _ (_ :< WeakTermEpsilonIntro l) branchList) = do
  let (caseList, _) = unzip branchList
  CaseLiteral l `elem` caseList || CaseDefault `elem` caseList
isReducible (_ :< WeakTermEpsilonElim (_, _) e _) = isReducible e
isReducible (_ :< WeakTermPi _) = False
isReducible (_ :< WeakTermPiIntro _ _) = False
isReducible (_ :< WeakTermPiElim (_ :< WeakTermPiIntro xts _) es)
  | length xts == length es = True
isReducible (_ :< WeakTermPiElim (_ :< WeakTermMu _ _) _) = True -- CBV recursion
isReducible (_ :< WeakTermPiElim (_ :< WeakTermConst c) [_ :< WeakTermEpsilonIntro (LiteralInteger _), _ :< WeakTermEpsilonIntro (LiteralInteger _)]) -- constant application
  | c `elem` intArithConstantList = True
isReducible (_ :< WeakTermPiElim e es) = isReducible e || any isReducible es
isReducible (_ :< WeakTermSigma _) = False
isReducible (_ :< WeakTermSigmaIntro es) = any isReducible es
isReducible (_ :< WeakTermSigmaElim xts (_ :< WeakTermSigmaIntro es) _)
  | length xts == length es = True
isReducible (_ :< WeakTermSigmaElim _ e1 _) = isReducible e1
isReducible (_ :< WeakTermTau _) = False
isReducible (_ :< WeakTermTauIntro e) = isReducible e
isReducible (_ :< WeakTermTauElim e) = isReducible e
isReducible (_ :< WeakTermTheta _) = False
isReducible (_ :< WeakTermThetaIntro e) = isReducible e
isReducible (_ :< WeakTermThetaElim e) = isReducible e
isReducible (_ :< WeakTermMu _ _) = False
isReducible (_ :< WeakTermIota e _) = isReducible e
isReducible (_ :< WeakTermConst _) = False
isReducible (_ :< WeakTermHole _) = False

toWeakTermPiElimSeq :: WeakTerm -> (WeakTerm, [(Identifier, [WeakTerm])])
toWeakTermPiElimSeq (i :< WeakTermPiElim e es) = do
  let (fun, xs) = toWeakTermPiElimSeq e
  (fun, xs ++ [(i, es)])
toWeakTermPiElimSeq c = (c, [])

isValue :: WeakTerm -> Bool
isValue (_ :< WeakTermUniv _)         = True
isValue (_ :< WeakTermUpsilon _)      = True
isValue (_ :< WeakTermEpsilon _)      = True
isValue (_ :< WeakTermEpsilonIntro _) = True
isValue (_ :< WeakTermPi {})          = True
isValue (_ :< WeakTermPiIntro _ _)    = True
isValue (_ :< WeakTermSigma {})       = True
isValue (_ :< WeakTermSigmaIntro es)  = all isValue es
isValue _                             = False
