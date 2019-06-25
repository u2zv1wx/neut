{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

module Data.WeakTerm where

import           Control.Comonad.Cofree
import           Control.Monad          (forM)
import           Data.Maybe             (fromMaybe)
import           Text.Show.Deriving

import           Data.Basic

type WeakUpsilon = (WeakSortal, Identifier)

type WeakUpsilonPlus = (WeakTerm, WeakUpsilon)

data WeakTermF a
  = WeakTermUniv UnivLevel
  | WeakTermUpsilon WeakUpsilon
  | WeakTermEpsilon Identifier
  | WeakTermEpsilonIntro Literal
  | WeakTermEpsilonElim (a, WeakUpsilon)
                        a
                        [(Case, a)]
  | WeakTermPi WeakSortal
               [(a, WeakUpsilon)]
  | WeakTermPiIntro WeakSortal
                    [(a, WeakUpsilon)]
                    a
  | WeakTermPiElim WeakSortal
                   a
                   [a]
  | WeakTermSigma WeakSortal
                  [(a, WeakUpsilon)]
  | WeakTermSigmaIntro WeakSortal
                       [a]
  | WeakTermSigmaElim WeakSortal
                      [(a, WeakUpsilon)]
                      a
                      a
  | WeakTermRec (a, WeakUpsilon)
                a
  | WeakTermConst Identifier
  | WeakTermHole Identifier

type WeakTerm = Cofree WeakTermF Identifier

type WeakSortal = WeakTerm

type DUpsilon = (DSortal, Identifier)

data DTermF a
  = DTermUniv UnivLevel
  | DTermDUpsilon DUpsilon
  | DTermEpsilon Identifier
  | DTermEpsilonIntro Literal
  | DTermEpsilonElim (DUpsilon, a)
                     a
                     [(Case, a)]
  | DTermPi DSortal
            [(DUpsilon, a)]
  | DTermPiIntro DSortal
                 [(DUpsilon, a)]
                 a
  | DTermPiElim DSortal
                a
                [a]
  | DTermSigma DSortal
               [(DUpsilon, a)]
  | DTermSigmaIntro DSortal
                    [a]
  | DTermSigmaElim DSortal
                   [(DUpsilon, a)]
                   a
                   a
  | DTermRec (DUpsilon, a)
             a
  | DTermConst Identifier
  | DTermHole Identifier

type DTerm = Cofree DTermF Identifier

type DSortal = DTerm

$(deriveShow1 ''DTermF)

type SubstWeakTerm = [(Identifier, WeakTerm)]

varWeakTerm :: WeakTerm -> [Identifier]
varWeakTerm e = fst $ varAndHole e

toDTerm :: WeakTerm -> DTerm
toDTerm (meta :< WeakTermUniv i) = meta :< DTermUniv i
toDTerm (meta :< WeakTermUpsilon (s, x)) = meta :< DTermDUpsilon (toDTerm s, x)
toDTerm (meta :< WeakTermEpsilon x) = meta :< DTermEpsilon x
toDTerm (meta :< WeakTermEpsilonIntro l) = meta :< DTermEpsilonIntro l
toDTerm (meta :< WeakTermEpsilonElim (t, (s, x)) e branchList) = do
  let (cs, es) = unzip branchList
  let es' = map toDTerm es
  let t' = toDTerm t
  meta :< DTermEpsilonElim ((toDTerm s, x), t') (toDTerm e) (zip cs es')
toDTerm (meta :< WeakTermPi s tus) = do
  let uts = toDTermUpsilonPlus tus
  let s' = toDTerm s
  meta :< DTermPi s' uts
toDTerm (meta :< WeakTermPiIntro s tus e) = do
  let s' = toDTerm s
  let uts = toDTermUpsilonPlus tus
  let e' = toDTerm e
  meta :< DTermPiIntro s' uts e'
toDTerm (meta :< WeakTermPiElim s e es) = do
  let s' = toDTerm s
  let e' = toDTerm e
  let es' = map toDTerm es
  meta :< DTermPiElim s' e' es'
toDTerm (meta :< WeakTermSigma s tus) = do
  let uts = toDTermUpsilonPlus tus
  let s' = toDTerm s
  meta :< DTermSigma s' uts
toDTerm (meta :< WeakTermSigmaIntro s es) = do
  let s' = toDTerm s
  let es' = map toDTerm es
  meta :< DTermSigmaIntro s' es'
toDTerm (meta :< WeakTermSigmaElim s tus e1 e2) = do
  let s' = toDTerm s
  let uts = toDTermUpsilonPlus tus
  let e1' = toDTerm e1
  let e2' = toDTerm e2
  meta :< DTermSigmaElim s' uts e1' e2'
toDTerm (meta :< WeakTermRec (t, u) e) =
  meta :< DTermRec (toDTermUpsilon u, toDTerm t) (toDTerm e)
toDTerm (meta :< WeakTermConst c) = meta :< DTermConst c
toDTerm (meta :< WeakTermHole x) = meta :< DTermHole x

toDTermUpsilon :: WeakUpsilon -> DUpsilon
toDTermUpsilon (s, x) = (toDTerm s, x)

toDTermUpsilonPlus :: [WeakUpsilonPlus] -> [(DUpsilon, DTerm)]
toDTermUpsilonPlus [] = []
toDTermUpsilonPlus ((t, u):tus) =
  (toDTermUpsilon u, toDTerm t) : toDTermUpsilonPlus tus

varAndHole :: WeakTerm -> ([Identifier], [Identifier])
varAndHole (_ :< WeakTermUniv _) = ([], [])
varAndHole (_ :< WeakTermUpsilon (s, x)) = do
  let (xs, hs) = varAndHole s
  (x : xs, hs)
varAndHole (_ :< WeakTermEpsilon _) = ([], [])
varAndHole (_ :< WeakTermEpsilonIntro _) = ([], [])
varAndHole (_ :< WeakTermEpsilonElim (t, (s, x)) e branchList) = do
  let xhs1 = varAndHole s
  let xhs2 = varAndHole t
  let xhs3 = varAndHole e
  xhss <-
    forM branchList $ \(_, body) -> do
      let (xs, hs) = varAndHole body
      return (filter (/= x) xs, hs)
  pairwiseConcat (xhs1 : xhs2 : xhs3 : xhss)
varAndHole (_ :< WeakTermPi s tus) = do
  let (xs1, hs1) = varAndHole s
  let (xs2, hs2) = varAndHoleBindings tus []
  (xs1 ++ xs2, hs1 ++ hs2)
varAndHole (_ :< WeakTermPiIntro s tus e) = do
  let (xs1, hs1) = varAndHole s
  let (xs2, hs2) = varAndHoleBindings tus [e]
  (xs1 ++ xs2, hs1 ++ hs2)
varAndHole (_ :< WeakTermPiElim s e es) =
  pairwiseConcat (varAndHole s : varAndHole e : map varAndHole es)
varAndHole (_ :< WeakTermSigma s tus) =
  pairwiseConcat [varAndHole s, varAndHoleBindings tus []]
varAndHole (_ :< WeakTermSigmaIntro s es) =
  pairwiseConcat $ varAndHole s : map varAndHole es
varAndHole (_ :< WeakTermSigmaElim s us e1 e2) =
  pairwiseConcat [varAndHole e1, varAndHole s, varAndHoleBindings us [e2]]
varAndHole (_ :< WeakTermRec ut e) = varAndHoleBindings [ut] [e]
varAndHole (_ :< WeakTermConst _) = ([], [])
varAndHole (_ :< WeakTermHole x) = ([], [x])

varAndHoleBindings ::
     [WeakUpsilonPlus] -> [WeakTerm] -> ([Identifier], [Identifier])
varAndHoleBindings [] es = pairwiseConcat $ map varAndHole es
varAndHoleBindings ((t, (s, x)):tus) es = do
  let (xs1, hs1) = varAndHole s
  let (xs2, hs2) = varAndHole t
  let (xs3, hs3) = varAndHoleBindings tus es
  (xs1 ++ xs2 ++ filter (/= x) xs3, hs1 ++ hs2 ++ hs3)

pairwiseConcat :: [([a], [b])] -> ([a], [b])
pairwiseConcat [] = ([], [])
pairwiseConcat ((xs, ys):rest) = do
  let (xs', ys') = pairwiseConcat rest
  (xs ++ xs', ys ++ ys')

substWeakTerm :: SubstWeakTerm -> WeakTerm -> WeakTerm
substWeakTerm _ (j :< WeakTermUniv i) = j :< WeakTermUniv i
substWeakTerm sub (j :< WeakTermUpsilon (s, x)) = do
  let s' = substWeakTerm sub s
  fromMaybe (j :< WeakTermUpsilon (s', x)) (lookup x sub)
substWeakTerm _ (j :< WeakTermEpsilon x) = j :< WeakTermEpsilon x
substWeakTerm _ (j :< WeakTermEpsilonIntro l) = j :< WeakTermEpsilonIntro l
substWeakTerm sub (j :< WeakTermEpsilonElim (t, (s, x)) e branchList) = do
  let s' = substWeakTerm sub s
  let t' = substWeakTerm sub t
  let e' = substWeakTerm sub e
  let (caseList, es) = unzip branchList
  let sub' = filter (\(k, _) -> k /= x) sub
  let es' = map (substWeakTerm sub') es
  j :< WeakTermEpsilonElim (t', (s', x)) e' (zip caseList es')
substWeakTerm sub (j :< WeakTermPi s tus) = do
  let s' = substWeakTerm sub s
  let tus' = substWeakTermBindings sub tus
  j :< WeakTermPi s' tus'
substWeakTerm sub (j :< WeakTermPiIntro s tus body) = do
  let s' = substWeakTerm sub s
  let (tus', body') = substWeakTermBindingsWithBody sub tus body
  j :< WeakTermPiIntro s' tus' body'
substWeakTerm sub (j :< WeakTermPiElim s e es) = do
  let s' = substWeakTerm sub s
  let e' = substWeakTerm sub e
  let es' = map (substWeakTerm sub) es
  j :< WeakTermPiElim s' e' es'
substWeakTerm sub (j :< WeakTermSigma s tus) = do
  let s' = substWeakTerm sub s
  let tus' = substWeakTermBindings sub tus
  j :< WeakTermSigma s' tus'
substWeakTerm sub (j :< WeakTermSigmaIntro s es) = do
  let s' = substWeakTerm sub s
  let es' = map (substWeakTerm sub) es
  j :< WeakTermSigmaIntro s' es'
substWeakTerm sub (j :< WeakTermSigmaElim s tus e1 e2) = do
  let s' = substWeakTerm sub s
  let e1' = substWeakTerm sub e1
  let (tus', e2') = substWeakTermBindingsWithBody sub tus e2
  j :< WeakTermSigmaElim s' tus' e1' e2'
substWeakTerm sub (j :< WeakTermRec (t, (s, x)) e) = do
  let s' = substWeakTerm sub s
  let t' = substWeakTerm sub t
  let e' = substWeakTerm (filter (\(k, _) -> k /= x) sub) e
  j :< WeakTermRec (t', (s', x)) e'
substWeakTerm _ (j :< WeakTermConst t) = j :< WeakTermConst t
substWeakTerm sub (j :< WeakTermHole s) =
  fromMaybe (j :< WeakTermHole s) (lookup s sub)

substWeakTermBindings :: SubstWeakTerm -> [WeakUpsilonPlus] -> [WeakUpsilonPlus]
substWeakTermBindings _ [] = []
substWeakTermBindings sub ((t, (s, x)):tus) = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let tus' = substWeakTermBindings sub' tus
  (substWeakTerm sub t, (substWeakTerm sub s, x)) : tus'

substWeakTermBindingsWithBody ::
     SubstWeakTerm
  -> [WeakUpsilonPlus]
  -> WeakTerm
  -> ([WeakUpsilonPlus], WeakTerm)
substWeakTermBindingsWithBody sub [] e = ([], substWeakTerm sub e)
substWeakTermBindingsWithBody sub ((t, (s, x)):tus) e = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let (tus', e') = substWeakTermBindingsWithBody sub' tus e
  ((substWeakTerm sub t, (substWeakTerm sub s, x)) : tus', e')

isReducible :: WeakTerm -> Bool
isReducible (_ :< WeakTermUniv _) = False
isReducible (_ :< WeakTermUpsilon u) = isReducibleUpsilon u
isReducible (_ :< WeakTermEpsilon _) = False
isReducible (_ :< WeakTermEpsilonIntro _) = False
isReducible (_ :< WeakTermEpsilonElim _ (_ :< WeakTermEpsilonIntro l) branchList) = do
  let (caseList, _) = unzip branchList
  CaseLiteral l `elem` caseList || CaseDefault `elem` caseList
isReducible (_ :< WeakTermEpsilonElim (_, (s, _)) e _) =
  isReducible s || isReducible e
isReducible (_ :< WeakTermPi s tus) =
  isReducible s || any isReducibleUpsilon (map snd tus)
isReducible (_ :< WeakTermPiIntro s tus _) =
  isReducible s || any isReducibleUpsilon (map snd tus)
isReducible (_ :< WeakTermPiElim _ (_ :< WeakTermPiIntro _ tus _) es)
  | length tus == length es = True
isReducible (_ :< WeakTermPiElim _ (_ :< WeakTermRec _ _) _) = True -- CBV recursion
isReducible (_ :< WeakTermPiElim _ (_ :< WeakTermConst c) [_ :< WeakTermEpsilonIntro (LiteralInteger _), _ :< WeakTermEpsilonIntro (LiteralInteger _)]) -- constant application
  | c `elem` intArithConstantList = True
isReducible (_ :< WeakTermPiElim s e es) =
  isReducible s || isReducible e || any isReducible es
isReducible (_ :< WeakTermSigma s tus) =
  isReducible s || any isReducibleUpsilon (map snd tus)
isReducible (_ :< WeakTermSigmaIntro s es) = isReducible s || any isReducible es
isReducible (_ :< WeakTermSigmaElim _ tus (_ :< WeakTermSigmaIntro _ es) _)
  | length tus == length es = True
isReducible (_ :< WeakTermSigmaElim s tus e1 _) =
  any isReducibleUpsilon (map snd tus) || isReducible s || isReducible e1
isReducible (_ :< WeakTermRec (_, u) _) = isReducibleUpsilon u
isReducible (_ :< WeakTermConst _) = False
isReducible (_ :< WeakTermHole _) = False

isReducibleUpsilon :: WeakUpsilon -> Bool
isReducibleUpsilon (s, _) = isReducible s

toWeakTermPiElimSeq ::
     WeakTerm -> (WeakTerm, [(Identifier, WeakSortal, [WeakTerm])])
toWeakTermPiElimSeq (i :< WeakTermPiElim s e es) = do
  let (fun, xs) = toWeakTermPiElimSeq e
  (fun, xs ++ [(i, s, es)])
toWeakTermPiElimSeq c = (c, [])
