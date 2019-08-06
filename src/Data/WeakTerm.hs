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
                  Int
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
  | WeakTermPi WeakLevel
               [(Identifier, a)]
  | WeakTermPiIntro WeakLevel
                    [(Identifier, a)]
                    a
  | WeakTermPiElim WeakLevel
                   a
                   [a]
  | WeakTermSigma WeakLevel
                  [(Identifier, a)]
  | WeakTermSigmaIntro WeakLevel
                       [a]
  | WeakTermSigmaElim WeakLevel
                      [(Identifier, a)]
                      a
                      a
  | WeakTermTau WeakLevel
                a -- K modality
  | WeakTermTauIntro WeakLevel
                     a
  | WeakTermTauElim WeakLevel
                    a
  | WeakTermTheta a -- S4 modality
  | WeakTermThetaIntro a
  | WeakTermThetaElim a
                      WeakLevel
  | WeakTermMu (Identifier, a)
               a
  | WeakTermConst Identifier
  | WeakTermHole Identifier
                 Int -- level diff

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
varAndHole (_ :< WeakTermPi i xts) =
  pairwiseConcat [varAndHoleLevel i, varAndHoleBindings xts []]
varAndHole (_ :< WeakTermPiIntro i xts e) =
  pairwiseConcat [varAndHoleLevel i, varAndHoleBindings xts [e]]
varAndHole (_ :< WeakTermPiElim i e es) =
  pairwiseConcat $ varAndHoleLevel i : varAndHole e : map varAndHole es
varAndHole (_ :< WeakTermSigma i xts) =
  pairwiseConcat [varAndHoleLevel i, varAndHoleBindings xts []]
varAndHole (_ :< WeakTermSigmaIntro i es) =
  pairwiseConcat $ varAndHoleLevel i : map varAndHole es
varAndHole (_ :< WeakTermSigmaElim i us e1 e2) =
  pairwiseConcat [varAndHoleLevel i, varAndHole e1, varAndHoleBindings us [e2]]
varAndHole (_ :< WeakTermTau i t) =
  pairwiseConcat [varAndHoleLevel i, varAndHole t]
varAndHole (_ :< WeakTermTauIntro i e) =
  pairwiseConcat [varAndHoleLevel i, varAndHole e]
varAndHole (_ :< WeakTermTauElim i e) =
  pairwiseConcat [varAndHoleLevel i, varAndHole e]
varAndHole (_ :< WeakTermTheta t) = varAndHole t
varAndHole (_ :< WeakTermThetaIntro e) = varAndHole e
varAndHole (_ :< WeakTermThetaElim e i) =
  pairwiseConcat [varAndHole e, varAndHoleLevel i]
varAndHole (_ :< WeakTermMu ut e) = varAndHoleBindings [ut] [e]
varAndHole (_ :< WeakTermConst _) = ([], [])
varAndHole (_ :< WeakTermHole x _) = ([], [x])

varAndHoleBindings ::
     [IdentifierPlus] -> [WeakTerm] -> ([Identifier], [Identifier])
varAndHoleBindings [] es = pairwiseConcat $ map varAndHole es
varAndHoleBindings ((x, t):xts) es = do
  let (xs1, hs1) = varAndHole t
  let (xs2, hs2) = varAndHoleBindings xts es
  (xs1 ++ filter (/= x) xs2, hs1 ++ hs2)

varAndHoleLevel :: WeakLevel -> ([Identifier], [Identifier])
varAndHoleLevel (WeakLevelHole h _) = ([], [h])
varAndHoleLevel _                   = ([], [])

pairwiseConcat :: [([a], [b])] -> ([a], [b])
pairwiseConcat [] = ([], [])
pairwiseConcat ((xs, ys):rest) = do
  let (xs', ys') = pairwiseConcat rest
  (xs ++ xs', ys ++ ys')

substWeakTerm :: SubstWeakTerm -> WeakTerm -> WeakTerm
substWeakTerm _ (m :< WeakTermUniv i) = m :< WeakTermUniv i
substWeakTerm sub (m :< WeakTermUpsilon x) =
  fromMaybe (m :< WeakTermUpsilon x) (lookup x sub)
substWeakTerm _ (m :< WeakTermEpsilon x) = m :< WeakTermEpsilon x
substWeakTerm _ (m :< WeakTermEpsilonIntro l) = m :< WeakTermEpsilonIntro l
substWeakTerm sub (m :< WeakTermEpsilonElim (x, t) e branchList) = do
  let t' = substWeakTerm sub t
  let e' = substWeakTerm sub e
  let (caseList, es) = unzip branchList
  let sub' = filter (\(k, _) -> k /= x) sub
  let es' = map (substWeakTerm sub') es
  m :< WeakTermEpsilonElim (x, t') e' (zip caseList es')
substWeakTerm sub (m :< WeakTermPi i xts) = do
  let xts' = substWeakTermBindings sub xts
  m :< WeakTermPi i xts'
substWeakTerm sub (m :< WeakTermPiIntro i xts body) = do
  let (xts', body') = substWeakTermBindingsWithBody sub xts body
  m :< WeakTermPiIntro i xts' body'
substWeakTerm sub (m :< WeakTermPiElim i e es) = do
  let e' = substWeakTerm sub e
  let es' = map (substWeakTerm sub) es
  m :< WeakTermPiElim i e' es'
substWeakTerm sub (m :< WeakTermSigma i xts) = do
  let xts' = substWeakTermBindings sub xts
  m :< WeakTermSigma i xts'
substWeakTerm sub (m :< WeakTermSigmaIntro i es) = do
  let es' = map (substWeakTerm sub) es
  m :< WeakTermSigmaIntro i es'
substWeakTerm sub (m :< WeakTermSigmaElim i xts e1 e2) = do
  let e1' = substWeakTerm sub e1
  let (xts', e2') = substWeakTermBindingsWithBody sub xts e2
  m :< WeakTermSigmaElim i xts' e1' e2'
substWeakTerm sub (m :< WeakTermTau i t) =
  m :< WeakTermTau i (substWeakTerm sub t)
substWeakTerm sub (m :< WeakTermTauIntro i e) =
  m :< WeakTermTauIntro i (substWeakTerm sub e)
substWeakTerm sub (m :< WeakTermTauElim i e) =
  m :< WeakTermTauElim i (substWeakTerm sub e)
substWeakTerm sub (m :< WeakTermTheta t) =
  m :< WeakTermTheta (substWeakTerm sub t)
substWeakTerm sub (m :< WeakTermThetaIntro e) =
  m :< WeakTermThetaIntro (substWeakTerm sub e)
substWeakTerm sub (m :< WeakTermThetaElim e i) =
  m :< WeakTermThetaElim (substWeakTerm sub e) i
substWeakTerm sub (m :< WeakTermMu (x, t) e) = do
  let t' = substWeakTerm sub t
  let e' = substWeakTerm (filter (\(k, _) -> k /= x) sub) e
  m :< WeakTermMu (x, t') e'
substWeakTerm _ (m :< WeakTermConst t) = m :< WeakTermConst t
substWeakTerm sub (m :< WeakTermHole s i) =
  fromMaybe (m :< WeakTermHole s i) (lookup s sub)

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

substWeakLevel :: SubstWeakLevel -> WeakTerm -> WeakTerm
substWeakLevel _ (m :< WeakTermUniv i) = m :< WeakTermUniv i
substWeakLevel _ (m :< WeakTermUpsilon x) = m :< WeakTermUpsilon x
substWeakLevel _ (m :< WeakTermEpsilon x) = m :< WeakTermEpsilon x
substWeakLevel _ (m :< WeakTermEpsilonIntro l) = m :< WeakTermEpsilonIntro l
substWeakLevel sub (m :< WeakTermEpsilonElim (x, t) e branchList) = do
  let t' = substWeakLevel sub t
  let e' = substWeakLevel sub e
  let (caseList, es) = unzip branchList
  let sub' = filter (\(k, _) -> k /= x) sub
  let es' = map (substWeakLevel sub') es
  m :< WeakTermEpsilonElim (x, t') e' (zip caseList es')
substWeakLevel sub (m :< WeakTermPi i xts) = do
  let xts' = substWeakLevelBindings sub xts
  m :< WeakTermPi (substWeakLevel' sub i) xts'
substWeakLevel sub (m :< WeakTermPiIntro i xts body) = do
  let (xts', body') = substWeakLevelBindingsWithBody sub xts body
  m :< WeakTermPiIntro (substWeakLevel' sub i) xts' body'
substWeakLevel sub (m :< WeakTermPiElim i e es) = do
  let e' = substWeakLevel sub e
  let es' = map (substWeakLevel sub) es
  m :< WeakTermPiElim (substWeakLevel' sub i) e' es'
substWeakLevel sub (m :< WeakTermSigma i xts) = do
  let xts' = substWeakLevelBindings sub xts
  m :< WeakTermSigma (substWeakLevel' sub i) xts'
substWeakLevel sub (m :< WeakTermSigmaIntro i es) = do
  let es' = map (substWeakLevel sub) es
  m :< WeakTermSigmaIntro (substWeakLevel' sub i) es'
substWeakLevel sub (m :< WeakTermSigmaElim i xts e1 e2) = do
  let e1' = substWeakLevel sub e1
  let (xts', e2') = substWeakLevelBindingsWithBody sub xts e2
  m :< WeakTermSigmaElim (substWeakLevel' sub i) xts' e1' e2'
substWeakLevel sub (m :< WeakTermTau i t) =
  m :< WeakTermTau (substWeakLevel' sub i) (substWeakLevel sub t)
substWeakLevel sub (m :< WeakTermTauIntro i e) =
  m :< WeakTermTauIntro (substWeakLevel' sub i) (substWeakLevel sub e)
substWeakLevel sub (m :< WeakTermTauElim i e) =
  m :< WeakTermTauElim (substWeakLevel' sub i) (substWeakLevel sub e)
substWeakLevel sub (m :< WeakTermTheta t) =
  m :< WeakTermTheta (substWeakLevel sub t)
substWeakLevel sub (m :< WeakTermThetaIntro e) =
  m :< WeakTermThetaIntro (substWeakLevel sub e)
substWeakLevel sub (m :< WeakTermThetaElim e i) =
  m :< WeakTermThetaElim (substWeakLevel sub e) (substWeakLevel' sub i)
substWeakLevel sub (m :< WeakTermMu (x, t) e) = do
  let t' = substWeakLevel sub t
  let e' = substWeakLevel (filter (\(k, _) -> k /= x) sub) e
  m :< WeakTermMu (x, t') e'
substWeakLevel _ (m :< WeakTermConst t) = m :< WeakTermConst t
substWeakLevel _ (m :< WeakTermHole s i) = m :< WeakTermHole s i

substWeakLevel' :: SubstWeakLevel -> WeakLevel -> WeakLevel
substWeakLevel' _ (WeakLevelInt i) = WeakLevelInt i
substWeakLevel' _ WeakLevelInfinity = WeakLevelInfinity
substWeakLevel' sub (WeakLevelHole h i) =
  fromMaybe (WeakLevelHole h i) (lookup h sub)

substWeakLevelBindings :: SubstWeakLevel -> [IdentifierPlus] -> [IdentifierPlus]
substWeakLevelBindings _ [] = []
substWeakLevelBindings sub ((x, t):xts) = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let xts' = substWeakLevelBindings sub' xts
  (x, substWeakLevel sub t) : xts'

substWeakLevelBindingsWithBody ::
     SubstWeakLevel
  -> [IdentifierPlus]
  -> WeakTerm
  -> ([IdentifierPlus], WeakTerm)
substWeakLevelBindingsWithBody sub [] e = ([], substWeakLevel sub e)
substWeakLevelBindingsWithBody sub ((x, t):xts) e = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let (xts', e') = substWeakLevelBindingsWithBody sub' xts e
  ((x, substWeakLevel sub t) : xts', e')

-- compute A^{+i}
shiftWeakTerm :: Int -> WeakTerm -> WeakTerm
shiftWeakTerm _ (m :< WeakTermUniv i) = m :< WeakTermUniv i
shiftWeakTerm _ (m :< WeakTermUpsilon x) = m :< WeakTermUpsilon x
shiftWeakTerm _ (m :< WeakTermEpsilon x) = m :< WeakTermEpsilon x
shiftWeakTerm _ (m :< WeakTermEpsilonIntro l) = m :< WeakTermEpsilonIntro l
shiftWeakTerm k (m :< WeakTermEpsilonElim (x, t) e branchList) = do
  let t' = shiftWeakTerm k t
  let e' = shiftWeakTerm k e
  let (caseList, es) = unzip branchList
  let es' = map (shiftWeakTerm k) es
  m :< WeakTermEpsilonElim (x, t') e' (zip caseList es')
shiftWeakTerm k (m :< WeakTermPi i xts) = do
  let xts' = shiftWeakTermBindings k xts
  m :< WeakTermPi (shiftWeakLevel k i) xts'
shiftWeakTerm k (m :< WeakTermPiIntro i xts body) = do
  let (xts', body') = shiftWeakTermBindingsWithBody k xts body
  m :< WeakTermPiIntro (shiftWeakLevel k i) xts' body'
shiftWeakTerm k (m :< WeakTermPiElim i e es) = do
  let e' = shiftWeakTerm k e
  let es' = map (shiftWeakTerm k) es
  m :< WeakTermPiElim (shiftWeakLevel k i) e' es'
shiftWeakTerm k (m :< WeakTermSigma i xts) = do
  let xts' = shiftWeakTermBindings k xts
  m :< WeakTermSigma (shiftWeakLevel k i) xts'
shiftWeakTerm k (m :< WeakTermSigmaIntro i es) = do
  let es' = map (shiftWeakTerm k) es
  m :< WeakTermSigmaIntro (shiftWeakLevel k i) es'
shiftWeakTerm k (m :< WeakTermSigmaElim i xts e1 e2) = do
  let e1' = shiftWeakTerm k e1
  let (xts', e2') = shiftWeakTermBindingsWithBody k xts e2
  m :< WeakTermSigmaElim (shiftWeakLevel k i) xts' e1' e2'
shiftWeakTerm k (m :< WeakTermTau i t) =
  m :< WeakTermTau (shiftWeakLevel k i) (shiftWeakTerm k t)
shiftWeakTerm k (m :< WeakTermTauIntro i e) =
  m :< WeakTermTauIntro (shiftWeakLevel k i) (shiftWeakTerm k e)
shiftWeakTerm k (m :< WeakTermTauElim i e) =
  m :< WeakTermTauElim (shiftWeakLevel k i) (shiftWeakTerm k e)
shiftWeakTerm k (m :< WeakTermTheta t) = m :< WeakTermTheta (shiftWeakTerm k t)
shiftWeakTerm k (m :< WeakTermThetaIntro e) =
  m :< WeakTermThetaIntro (shiftWeakTerm k e)
shiftWeakTerm k (m :< WeakTermThetaElim e i) =
  m :< WeakTermThetaElim e (shiftWeakLevel k i)
shiftWeakTerm k (m :< WeakTermMu (x, t) e) = do
  let t' = shiftWeakTerm k t
  let e' = shiftWeakTerm k e
  m :< WeakTermMu (x, t') e'
shiftWeakTerm _ (m :< WeakTermConst t) = m :< WeakTermConst t
shiftWeakTerm k (m :< WeakTermHole s i) = m :< WeakTermHole s (i + k)

shiftWeakTermBindings :: Int -> [IdentifierPlus] -> [IdentifierPlus]
shiftWeakTermBindings _ [] = []
shiftWeakTermBindings i ((x, t):xts) = do
  let xts' = shiftWeakTermBindings i xts
  (x, shiftWeakTerm i t) : xts'

shiftWeakTermBindingsWithBody ::
     Int -> [IdentifierPlus] -> WeakTerm -> ([IdentifierPlus], WeakTerm)
shiftWeakTermBindingsWithBody i [] e = ([], shiftWeakTerm i e)
shiftWeakTermBindingsWithBody i ((x, t):xts) e = do
  let (xts', e') = shiftWeakTermBindingsWithBody i xts e
  ((x, shiftWeakTerm i t) : xts', e')

shiftWeakLevel :: Int -> WeakLevel -> WeakLevel
shiftWeakLevel k (WeakLevelInt i)    = WeakLevelInt (i + k)
shiftWeakLevel _ WeakLevelInfinity   = WeakLevelInfinity
shiftWeakLevel k (WeakLevelHole h i) = WeakLevelHole h (i + k)

-- TODO: reduceのときにレベルについての条件を追加すべき
isReducible :: WeakTerm -> Bool
isReducible (_ :< WeakTermUniv _) = False
isReducible (_ :< WeakTermUpsilon _) = False
isReducible (_ :< WeakTermEpsilon _) = False
isReducible (_ :< WeakTermEpsilonIntro _) = False
isReducible (_ :< WeakTermEpsilonElim _ (_ :< WeakTermEpsilonIntro l) branchList) = do
  let (caseList, _) = unzip branchList
  CaseLiteral l `elem` caseList || CaseDefault `elem` caseList
isReducible (_ :< WeakTermEpsilonElim (_, _) e _) = isReducible e
isReducible (_ :< WeakTermPi _ _) = False
isReducible (_ :< WeakTermPiIntro {}) = False
isReducible (_ :< WeakTermPiElim _ (_ :< WeakTermPiIntro _ xts _) es)
  | length xts == length es = True
isReducible (_ :< WeakTermPiElim _ (_ :< WeakTermMu _ _) _) = True -- CBV recursion
isReducible (_ :< WeakTermPiElim _ (_ :< WeakTermConst c) [_ :< WeakTermEpsilonIntro (LiteralInteger _), _ :< WeakTermEpsilonIntro (LiteralInteger _)]) -- constant application
  | c `elem` intArithConstantList = True
isReducible (_ :< WeakTermPiElim _ e es) = isReducible e || any isReducible es
isReducible (_ :< WeakTermSigma _ _) = False
isReducible (_ :< WeakTermSigmaIntro _ es) = any isReducible es
isReducible (_ :< WeakTermSigmaElim _ xts (_ :< WeakTermSigmaIntro _ es) _)
  | length xts == length es = True
isReducible (_ :< WeakTermSigmaElim _ _ e1 _) = isReducible e1
isReducible (_ :< WeakTermTau _ _) = False
isReducible (_ :< WeakTermTauIntro _ e) = isReducible e
isReducible (_ :< WeakTermTauElim i (_ :< WeakTermTauIntro j _))
  | i == j = True
isReducible (_ :< WeakTermTauElim _ e) = isReducible e
isReducible (_ :< WeakTermTheta _) = False
isReducible (_ :< WeakTermThetaIntro e) = isReducible e
isReducible (_ :< WeakTermThetaElim (_ :< WeakTermThetaIntro _) _) = True
isReducible (_ :< WeakTermThetaElim e _) = isReducible e
isReducible (_ :< WeakTermMu _ _) = False
isReducible (_ :< WeakTermConst _) = False
isReducible (_ :< WeakTermHole _ _) = False

toWeakTermPiElimSeq :: WeakTerm -> (WeakTerm, [(Identifier, [WeakTerm])])
toWeakTermPiElimSeq (m :< WeakTermPiElim _ e es) = do
  let (fun, xs) = toWeakTermPiElimSeq e
  (fun, xs ++ [(m, es)])
toWeakTermPiElimSeq c = (c, [])

isValue :: WeakTerm -> Bool
isValue (_ :< WeakTermUniv _)          = True
isValue (_ :< WeakTermUpsilon _)       = True
isValue (_ :< WeakTermEpsilon _)       = True
isValue (_ :< WeakTermEpsilonIntro _)  = True
isValue (_ :< WeakTermPi {})           = True
isValue (_ :< WeakTermPiIntro {})      = True
isValue (_ :< WeakTermSigma {})        = True
isValue (_ :< WeakTermSigmaIntro _ es) = all isValue es
isValue _                              = False
