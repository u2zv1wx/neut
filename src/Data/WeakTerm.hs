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

data WeakSortal
  = WeakSortalPrimitive
  | WeakSortalTerm WeakTerm

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
  | WeakTermAscription a
                       a
  | WeakTermHole Identifier

type WeakTerm = Cofree WeakTermF Identifier

type DUpsilon = (DSortal, Identifier)

data DSortal
  = DSortalPrimitive
  | DSortalTerm DTerm

deriving instance Show DSortal

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
  | DTermAscription a
                    a
  | DTermHole Identifier

type DTerm = Cofree DTermF Identifier

$(deriveShow1 ''DTermF)

type SubstWeakTerm = [(Identifier, WeakTerm)]

varWeakTerm :: WeakTerm -> [Identifier]
varWeakTerm e = fst $ varAndHole e

toDTerm :: WeakTerm -> DTerm
toDTerm (meta :< WeakTermUniv i) = meta :< DTermUniv i
toDTerm (meta :< WeakTermUpsilon (s, x)) =
  meta :< DTermDUpsilon (toDTermSortal s, x)
toDTerm (meta :< WeakTermEpsilon x) = meta :< DTermEpsilon x
toDTerm (meta :< WeakTermEpsilonIntro l) = meta :< DTermEpsilonIntro l
toDTerm (meta :< WeakTermEpsilonElim (t, (s, x)) e branchList) = do
  let (cs, es) = unzip branchList
  let es' = map toDTerm es
  let t' = toDTerm t
  meta :< DTermEpsilonElim ((toDTermSortal s, x), t') (toDTerm e) (zip cs es')
toDTerm (meta :< WeakTermPi s tus) = do
  let uts = toDTermUpsilonPlus tus
  let s' = toDTermSortal s
  meta :< DTermPi s' uts
toDTerm (meta :< WeakTermPiIntro s tus e) = do
  let s' = toDTermSortal s
  let uts = toDTermUpsilonPlus tus
  let e' = toDTerm e
  meta :< DTermPiIntro s' uts e'
toDTerm (meta :< WeakTermPiElim s e es) = do
  let s' = toDTermSortal s
  let e' = toDTerm e
  let es' = map toDTerm es
  meta :< DTermPiElim s' e' es'
toDTerm (meta :< WeakTermSigma s tus) = do
  let uts = toDTermUpsilonPlus tus
  let s' = toDTermSortal s
  meta :< DTermSigma s' uts
toDTerm (meta :< WeakTermSigmaIntro s es) = do
  let s' = toDTermSortal s
  let es' = map toDTerm es
  meta :< DTermSigmaIntro s' es'
toDTerm (meta :< WeakTermSigmaElim s tus e1 e2) = do
  let s' = toDTermSortal s
  let uts = toDTermUpsilonPlus tus
  let e1' = toDTerm e1
  let e2' = toDTerm e2
  meta :< DTermSigmaElim s' uts e1' e2'
toDTerm (meta :< WeakTermRec (t, u) e) =
  meta :< DTermRec (toDTermUpsilon u, toDTerm t) (toDTerm e)
toDTerm (meta :< WeakTermConst c) = meta :< DTermConst c
toDTerm (meta :< WeakTermAscription t e) = do
  let t' = toDTerm t
  let e' = toDTerm e
  meta :< DTermAscription t' e'
toDTerm (meta :< WeakTermHole x) = meta :< DTermHole x

toDTermSortal :: WeakSortal -> DSortal
toDTermSortal WeakSortalPrimitive = DSortalPrimitive
toDTermSortal (WeakSortalTerm e)  = DSortalTerm $ toDTerm e

toDTermUpsilon :: WeakUpsilon -> DUpsilon
toDTermUpsilon (s, x) = (toDTermSortal s, x)

toDTermUpsilonPlus :: [WeakUpsilonPlus] -> [(DUpsilon, DTerm)]
toDTermUpsilonPlus [] = []
toDTermUpsilonPlus ((t, u):tus) =
  (toDTermUpsilon u, toDTerm t) : toDTermUpsilonPlus tus

varAndHole :: WeakTerm -> ([Identifier], [Identifier])
varAndHole (_ :< WeakTermUniv _) = ([], [])
varAndHole (_ :< WeakTermUpsilon (s, x)) = do
  let (xs, hs) = varAndHoleSortal s
  (x : xs, hs)
varAndHole (_ :< WeakTermEpsilon _) = ([], [])
varAndHole (_ :< WeakTermEpsilonIntro _) = ([], [])
varAndHole (_ :< WeakTermEpsilonElim (t, (s, x)) e branchList) = do
  let xhs1 = varAndHoleSortal s
  let xhs2 = varAndHole t
  let xhs3 = varAndHole e
  xhss <-
    forM branchList $ \(_, body) -> do
      let (xs, hs) = varAndHole body
      return (filter (/= x) xs, hs)
  pairwiseConcat (xhs1 : xhs2 : xhs3 : xhss)
varAndHole (_ :< WeakTermPi s tus) = do
  let (xs1, hs1) = varAndHoleSortal s
  let (xs2, hs2) = varAndHoleBindings tus []
  (xs1 ++ xs2, hs1 ++ hs2)
varAndHole (_ :< WeakTermPiIntro s tus e) = do
  let (xs1, hs1) = varAndHoleSortal s
  let (xs2, hs2) = varAndHoleBindings tus [e]
  (xs1 ++ xs2, hs1 ++ hs2)
varAndHole (_ :< WeakTermPiElim s e es) =
  pairwiseConcat (varAndHoleSortal s : varAndHole e : map varAndHole es)
varAndHole (_ :< WeakTermSigma s tus) =
  pairwiseConcat [varAndHoleSortal s, varAndHoleBindings tus []]
varAndHole (_ :< WeakTermSigmaIntro s es) =
  pairwiseConcat $ varAndHoleSortal s : map varAndHole es
varAndHole (_ :< WeakTermSigmaElim s us e1 e2) =
  pairwiseConcat [varAndHole e1, varAndHoleSortal s, varAndHoleBindings us [e2]]
varAndHole (_ :< WeakTermRec ut e) = varAndHoleBindings [ut] [e]
varAndHole (_ :< WeakTermConst _) = ([], [])
varAndHole (_ :< WeakTermAscription e t) =
  pairwiseConcat [varAndHole e, varAndHole t]
varAndHole (_ :< WeakTermHole x) = ([], [x])

varAndHoleSortal :: WeakSortal -> ([Identifier], [Identifier])
varAndHoleSortal WeakSortalPrimitive = ([], [])
varAndHoleSortal (WeakSortalTerm e)  = varAndHole e

varAndHoleBindings ::
     [WeakUpsilonPlus] -> [WeakTerm] -> ([Identifier], [Identifier])
varAndHoleBindings [] es = pairwiseConcat $ map varAndHole es
varAndHoleBindings ((t, (s, x)):tus) es = do
  let (xs1, hs1) = varAndHoleSortal s
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
  let s' = substWeakTermSortal sub s
  fromMaybe (j :< WeakTermUpsilon (s', x)) (lookup x sub)
substWeakTerm _ (j :< WeakTermEpsilon x) = j :< WeakTermEpsilon x
substWeakTerm _ (j :< WeakTermEpsilonIntro l) = j :< WeakTermEpsilonIntro l
substWeakTerm sub (j :< WeakTermEpsilonElim (t, (s, x)) e branchList) = do
  let s' = substWeakTermSortal sub s
  let t' = substWeakTerm sub t
  let e' = substWeakTerm sub e
  let (caseList, es) = unzip branchList
  let sub' = filter (\(k, _) -> k /= x) sub
  let es' = map (substWeakTerm sub') es
  j :< WeakTermEpsilonElim (t', (s', x)) e' (zip caseList es')
substWeakTerm sub (j :< WeakTermPi s tus) = do
  let s' = substWeakTermSortal sub s
  let tus' = substWeakTermBindings sub tus
  j :< WeakTermPi s' tus'
substWeakTerm sub (j :< WeakTermPiIntro s tus body) = do
  let s' = substWeakTermSortal sub s
  let (tus', body') = substWeakTermBindingsWithBody sub tus body
  j :< WeakTermPiIntro s' tus' body'
substWeakTerm sub (j :< WeakTermPiElim s e es) = do
  let s' = substWeakTermSortal sub s
  let e' = substWeakTerm sub e
  let es' = map (substWeakTerm sub) es
  j :< WeakTermPiElim s' e' es'
substWeakTerm sub (j :< WeakTermSigma s tus) = do
  let s' = substWeakTermSortal sub s
  let tus' = substWeakTermBindings sub tus
  j :< WeakTermSigma s' tus'
substWeakTerm sub (j :< WeakTermSigmaIntro s es) = do
  let s' = substWeakTermSortal sub s
  let es' = map (substWeakTerm sub) es
  j :< WeakTermSigmaIntro s' es'
substWeakTerm sub (j :< WeakTermSigmaElim s tus e1 e2) = do
  let s' = substWeakTermSortal sub s
  let e1' = substWeakTerm sub e1
  let (tus', e2') = substWeakTermBindingsWithBody sub tus e2
  j :< WeakTermSigmaElim s' tus' e1' e2'
substWeakTerm sub (j :< WeakTermRec (t, (s, x)) e) = do
  let s' = substWeakTermSortal sub s
  let t' = substWeakTerm sub t
  let e' = substWeakTerm (filter (\(k, _) -> k /= x) sub) e
  j :< WeakTermRec (t', (s', x)) e'
substWeakTerm _ (j :< WeakTermConst t) = j :< WeakTermConst t
substWeakTerm sub (j :< WeakTermAscription e t) = do
  let e' = substWeakTerm sub e
  let t' = substWeakTerm sub t
  j :< WeakTermAscription e' t'
substWeakTerm sub (j :< WeakTermHole s) =
  fromMaybe (j :< WeakTermHole s) (lookup s sub)

substWeakTermBindings :: SubstWeakTerm -> [WeakUpsilonPlus] -> [WeakUpsilonPlus]
substWeakTermBindings _ [] = []
substWeakTermBindings sub ((t, (s, x)):tus) = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let tus' = substWeakTermBindings sub' tus
  (substWeakTerm sub t, (substWeakTermSortal sub s, x)) : tus'

substWeakTermBindingsWithBody ::
     SubstWeakTerm
  -> [WeakUpsilonPlus]
  -> WeakTerm
  -> ([WeakUpsilonPlus], WeakTerm)
substWeakTermBindingsWithBody sub [] e = ([], substWeakTerm sub e)
substWeakTermBindingsWithBody sub ((t, (s, x)):tus) e = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let (tus', e') = substWeakTermBindingsWithBody sub' tus e
  ((substWeakTerm sub t, (substWeakTermSortal sub s, x)) : tus', e')

substWeakTermSortal :: SubstWeakTerm -> WeakSortal -> WeakSortal
substWeakTermSortal _ WeakSortalPrimitive = WeakSortalPrimitive
substWeakTermSortal sub (WeakSortalTerm e) =
  WeakSortalTerm $ substWeakTerm sub e

isReducible :: WeakTerm -> Bool
isReducible (_ :< WeakTermUniv _) = False
isReducible (_ :< WeakTermUpsilon u) = isReducibleUpsilon u
isReducible (_ :< WeakTermEpsilon _) = False
isReducible (_ :< WeakTermEpsilonIntro _) = False
isReducible (_ :< WeakTermEpsilonElim _ (_ :< WeakTermEpsilonIntro l) branchList) = do
  let (caseList, _) = unzip branchList
  CaseLiteral l `elem` caseList || CaseDefault `elem` caseList
isReducible (_ :< WeakTermEpsilonElim (_, (s, _)) e _) =
  isReducibleSortal s || isReducible e
isReducible (_ :< WeakTermPi s tus) =
  isReducibleSortal s || any isReducibleUpsilon (map snd tus)
isReducible (_ :< WeakTermPiIntro s tus _) =
  isReducibleSortal s || any isReducibleUpsilon (map snd tus)
isReducible (_ :< WeakTermPiElim _ (_ :< WeakTermPiIntro _ tus _) es)
  | length tus == length es = True
isReducible (_ :< WeakTermPiElim _ (_ :< WeakTermRec _ _) _) = True -- CBV recursion
isReducible (_ :< WeakTermPiElim _ (_ :< WeakTermConst c) [_ :< WeakTermEpsilonIntro (LiteralInteger _), _ :< WeakTermEpsilonIntro (LiteralInteger _)]) -- constant application
  | c `elem` intArithConstantList = True
isReducible (_ :< WeakTermPiElim s e es) =
  isReducibleSortal s || isReducible e || any isReducible es
isReducible (_ :< WeakTermSigma s tus) =
  isReducibleSortal s || any isReducibleUpsilon (map snd tus)
isReducible (_ :< WeakTermSigmaIntro s es) =
  isReducibleSortal s || any isReducible es
isReducible (_ :< WeakTermSigmaElim _ tus (_ :< WeakTermSigmaIntro _ es) _)
  | length tus == length es = True
isReducible (_ :< WeakTermSigmaElim s tus e1 _) =
  any isReducibleUpsilon (map snd tus) || isReducibleSortal s || isReducible e1
isReducible (_ :< WeakTermRec (_, u) _) = isReducibleUpsilon u
isReducible (_ :< WeakTermConst _) = False
isReducible (_ :< WeakTermAscription _ _) = True
isReducible (_ :< WeakTermHole _) = False

isReducibleSortal :: WeakSortal -> Bool
isReducibleSortal WeakSortalPrimitive = False
isReducibleSortal (WeakSortalTerm e)  = isReducible e

isReducibleUpsilon :: WeakUpsilon -> Bool
isReducibleUpsilon (s, _) = isReducibleSortal s

toWeakTermPiElimSeq ::
     WeakTerm -> (WeakTerm, [(Identifier, WeakSortal, [WeakTerm])])
toWeakTermPiElimSeq (i :< WeakTermPiElim s e es) = do
  let (fun, xs) = toWeakTermPiElimSeq e
  (fun, xs ++ [(i, s, es)])
toWeakTermPiElimSeq c = (c, [])
