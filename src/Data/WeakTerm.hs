{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

module Data.WeakTerm where

import           Control.Comonad.Cofree
import           Control.Monad          (forM)
import           Data.Maybe             (fromMaybe)
import           Text.Show.Deriving

import           Data.Basic

type IdentifierPlus = (WeakTerm, Identifier)

data WeakEpsilon
  = WeakEpsilonIdentifier Identifier
  | WeakEpsilonHole Identifier
  deriving (Show)

data WeakTermF a
  = WeakTermUniv UnivLevel
  | WeakTermUpsilon Identifier
  | WeakTermEpsilon WeakEpsilon
  | WeakTermEpsilonIntro Literal
  | WeakTermEpsilonElim (a, Identifier)
                        a
                        [(Case, a)]
  | WeakTermPi WeakSortal
               [(a, Identifier)]
  | WeakTermPiIntro WeakSortal
                    [(a, Identifier)]
                    a
  | WeakTermPiElim WeakSortal
                   a
                   [a]
  | WeakTermSigma WeakSortal
                  [(a, Identifier)]
  | WeakTermSigmaIntro WeakSortal
                       [a]
  | WeakTermSigmaElim WeakSortal
                      [(a, Identifier)]
                      a
                      a
  | WeakTermRec (a, Identifier)
                a
  | WeakTermConst Identifier
  | WeakTermHole Identifier

type WeakTerm = Cofree WeakTermF Identifier

type WeakSortal = WeakTerm

type DUpsilon = Identifier

data DTermF a
  = DTermUniv UnivLevel
  | DTermDUpsilon DUpsilon
  | DTermEpsilon WeakEpsilon
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
toDTerm (meta :< WeakTermUpsilon x) = meta :< DTermDUpsilon x
toDTerm (meta :< WeakTermEpsilon x) = meta :< DTermEpsilon x
toDTerm (meta :< WeakTermEpsilonIntro l) = meta :< DTermEpsilonIntro l
toDTerm (meta :< WeakTermEpsilonElim (t, x) e branchList) = do
  let (cs, es) = unzip branchList
  let es' = map toDTerm es
  let t' = toDTerm t
  meta :< DTermEpsilonElim (x, t') (toDTerm e) (zip cs es')
toDTerm (meta :< WeakTermPi s txs) = do
  let uts = toDTermUpsilonPlus txs
  let s' = toDTerm s
  meta :< DTermPi s' uts
toDTerm (meta :< WeakTermPiIntro s txs e) = do
  let s' = toDTerm s
  let uts = toDTermUpsilonPlus txs
  let e' = toDTerm e
  meta :< DTermPiIntro s' uts e'
toDTerm (meta :< WeakTermPiElim s e es) = do
  let s' = toDTerm s
  let e' = toDTerm e
  let es' = map toDTerm es
  meta :< DTermPiElim s' e' es'
toDTerm (meta :< WeakTermSigma s txs) = do
  let uts = toDTermUpsilonPlus txs
  let s' = toDTerm s
  meta :< DTermSigma s' uts
toDTerm (meta :< WeakTermSigmaIntro s es) = do
  let s' = toDTerm s
  let es' = map toDTerm es
  meta :< DTermSigmaIntro s' es'
toDTerm (meta :< WeakTermSigmaElim s txs e1 e2) = do
  let s' = toDTerm s
  let uts = toDTermUpsilonPlus txs
  let e1' = toDTerm e1
  let e2' = toDTerm e2
  meta :< DTermSigmaElim s' uts e1' e2'
toDTerm (meta :< WeakTermRec (t, u) e) =
  meta :< DTermRec (toDTermUpsilon u, toDTerm t) (toDTerm e)
toDTerm (meta :< WeakTermConst c) = meta :< DTermConst c
toDTerm (meta :< WeakTermHole x) = meta :< DTermHole x

toDTermUpsilon :: Identifier -> DUpsilon
toDTermUpsilon x = x

toDTermUpsilonPlus :: [IdentifierPlus] -> [(DUpsilon, DTerm)]
toDTermUpsilonPlus [] = []
toDTermUpsilonPlus ((t, u):txs) =
  (toDTermUpsilon u, toDTerm t) : toDTermUpsilonPlus txs

varAndHole :: WeakTerm -> ([Identifier], [Identifier])
varAndHole (_ :< WeakTermUniv _) = ([], [])
varAndHole (_ :< WeakTermUpsilon x) = ([x], [])
varAndHole (_ :< WeakTermEpsilon _) = ([], [])
varAndHole (_ :< WeakTermEpsilonIntro _) = ([], [])
varAndHole (_ :< WeakTermEpsilonElim (t, x) e branchList) = do
  let xhs1 = varAndHole t
  let xhs2 = varAndHole e
  xhss <-
    forM branchList $ \(_, body) -> do
      let (xs, hs) = varAndHole body
      return (filter (/= x) xs, hs)
  pairwiseConcat (xhs1 : xhs2 : xhss)
varAndHole (_ :< WeakTermPi s txs) = do
  let (xs1, hs1) = varAndHole s
  let (xs2, hs2) = varAndHoleBindings txs []
  (xs1 ++ xs2, hs1 ++ hs2)
varAndHole (_ :< WeakTermPiIntro s txs e) = do
  let (xs1, hs1) = varAndHole s
  let (xs2, hs2) = varAndHoleBindings txs [e]
  (xs1 ++ xs2, hs1 ++ hs2)
varAndHole (_ :< WeakTermPiElim s e es) =
  pairwiseConcat (varAndHole s : varAndHole e : map varAndHole es)
varAndHole (_ :< WeakTermSigma s txs) =
  pairwiseConcat [varAndHole s, varAndHoleBindings txs []]
varAndHole (_ :< WeakTermSigmaIntro s es) =
  pairwiseConcat $ varAndHole s : map varAndHole es
varAndHole (_ :< WeakTermSigmaElim s us e1 e2) =
  pairwiseConcat [varAndHole e1, varAndHole s, varAndHoleBindings us [e2]]
varAndHole (_ :< WeakTermRec ut e) = varAndHoleBindings [ut] [e]
varAndHole (_ :< WeakTermConst _) = ([], [])
varAndHole (_ :< WeakTermHole x) = ([], [x])

varAndHoleBindings ::
     [IdentifierPlus] -> [WeakTerm] -> ([Identifier], [Identifier])
varAndHoleBindings [] es = pairwiseConcat $ map varAndHole es
varAndHoleBindings ((t, x):txs) es = do
  let (xs1, hs1) = varAndHole t
  let (xs2, hs2) = varAndHoleBindings txs es
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
substWeakTerm sub (j :< WeakTermEpsilonElim (t, x) e branchList) = do
  let t' = substWeakTerm sub t
  let e' = substWeakTerm sub e
  let (caseList, es) = unzip branchList
  let sub' = filter (\(k, _) -> k /= x) sub
  let es' = map (substWeakTerm sub') es
  j :< WeakTermEpsilonElim (t', x) e' (zip caseList es')
substWeakTerm sub (j :< WeakTermPi s txs) = do
  let s' = substWeakTerm sub s
  let txs' = substWeakTermBindings sub txs
  j :< WeakTermPi s' txs'
substWeakTerm sub (j :< WeakTermPiIntro s txs body) = do
  let s' = substWeakTerm sub s
  let (txs', body') = substWeakTermBindingsWithBody sub txs body
  j :< WeakTermPiIntro s' txs' body'
substWeakTerm sub (j :< WeakTermPiElim s e es) = do
  let s' = substWeakTerm sub s
  let e' = substWeakTerm sub e
  let es' = map (substWeakTerm sub) es
  j :< WeakTermPiElim s' e' es'
substWeakTerm sub (j :< WeakTermSigma s txs) = do
  let s' = substWeakTerm sub s
  let txs' = substWeakTermBindings sub txs
  j :< WeakTermSigma s' txs'
substWeakTerm sub (j :< WeakTermSigmaIntro s es) = do
  let s' = substWeakTerm sub s
  let es' = map (substWeakTerm sub) es
  j :< WeakTermSigmaIntro s' es'
substWeakTerm sub (j :< WeakTermSigmaElim s txs e1 e2) = do
  let s' = substWeakTerm sub s
  let e1' = substWeakTerm sub e1
  let (txs', e2') = substWeakTermBindingsWithBody sub txs e2
  j :< WeakTermSigmaElim s' txs' e1' e2'
substWeakTerm sub (j :< WeakTermRec (t, x) e) = do
  let t' = substWeakTerm sub t
  let e' = substWeakTerm (filter (\(k, _) -> k /= x) sub) e
  j :< WeakTermRec (t', x) e'
substWeakTerm _ (j :< WeakTermConst t) = j :< WeakTermConst t
substWeakTerm sub (j :< WeakTermHole s) =
  fromMaybe (j :< WeakTermHole s) (lookup s sub)

substWeakTermBindings :: SubstWeakTerm -> [IdentifierPlus] -> [IdentifierPlus]
substWeakTermBindings _ [] = []
substWeakTermBindings sub ((t, x):txs) = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let txs' = substWeakTermBindings sub' txs
  (substWeakTerm sub t, x) : txs'

substWeakTermBindingsWithBody ::
     SubstWeakTerm
  -> [IdentifierPlus]
  -> WeakTerm
  -> ([IdentifierPlus], WeakTerm)
substWeakTermBindingsWithBody sub [] e = ([], substWeakTerm sub e)
substWeakTermBindingsWithBody sub ((t, x):txs) e = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let (txs', e') = substWeakTermBindingsWithBody sub' txs e
  ((substWeakTerm sub t, x) : txs', e')

isReducible :: WeakTerm -> Bool
isReducible (_ :< WeakTermUniv _) = False
isReducible (_ :< WeakTermUpsilon _) = False
isReducible (_ :< WeakTermEpsilon _) = False
isReducible (_ :< WeakTermEpsilonIntro _) = False
isReducible (_ :< WeakTermEpsilonElim _ (_ :< WeakTermEpsilonIntro l) branchList) = do
  let (caseList, _) = unzip branchList
  CaseLiteral l `elem` caseList || CaseDefault `elem` caseList
isReducible (_ :< WeakTermEpsilonElim (_, _) e _) = isReducible e
isReducible (_ :< WeakTermPi s _) = isReducible s
isReducible (_ :< WeakTermPiIntro s _ _) = isReducible s
isReducible (_ :< WeakTermPiElim _ (_ :< WeakTermPiIntro _ txs _) es)
  | length txs == length es = True
isReducible (_ :< WeakTermPiElim _ (_ :< WeakTermRec _ _) _) = True -- CBV recursion
isReducible (_ :< WeakTermPiElim _ (_ :< WeakTermConst c) [_ :< WeakTermEpsilonIntro (LiteralInteger _), _ :< WeakTermEpsilonIntro (LiteralInteger _)]) -- constant application
  | c `elem` intArithConstantList = True
isReducible (_ :< WeakTermPiElim s e es) =
  isReducible s || isReducible e || any isReducible es
isReducible (_ :< WeakTermSigma s _) = isReducible s
isReducible (_ :< WeakTermSigmaIntro s es) = isReducible s || any isReducible es
isReducible (_ :< WeakTermSigmaElim _ txs (_ :< WeakTermSigmaIntro _ es) _)
  | length txs == length es = True
isReducible (_ :< WeakTermSigmaElim s _ e1 _) = isReducible s || isReducible e1
isReducible (_ :< WeakTermRec _ _) = False
isReducible (_ :< WeakTermConst _) = False
isReducible (_ :< WeakTermHole _) = False

toWeakTermPiElimSeq ::
     WeakTerm -> (WeakTerm, [(Identifier, WeakSortal, [WeakTerm])])
toWeakTermPiElimSeq (i :< WeakTermPiElim s e es) = do
  let (fun, xs) = toWeakTermPiElimSeq e
  (fun, xs ++ [(i, s, es)])
toWeakTermPiElimSeq c = (c, [])
