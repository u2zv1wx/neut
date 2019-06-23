{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

module Data.WeakTerm where

import           Control.Comonad.Cofree
import           Control.Monad          (forM)
import           Data.Maybe             (fromMaybe)
import           Text.Show.Deriving

import           Data.Basic

type Upsilon = (Sortal, Identifier)

data Sortal
  = SortalPrimitive
  | SortalTerm WeakTerm

deriving instance Show Sortal

data WeakTermF a
  = WeakTermUpsilon Upsilon
  | WeakTermEpsilon Identifier
  | WeakTermEpsilonIntro Literal
  | WeakTermEpsilonElim a
                        [(Case, a)]
  | WeakTermPi Sortal
               [(Upsilon, a)]
  | WeakTermPiIntro Sortal
                    [(Upsilon, a)]
                    a
  | WeakTermPiElim Sortal
                   a
                   [a]
  | WeakTermSigma Sortal
                  [(Upsilon, a)]
  | WeakTermSigmaIntro Sortal
                       [a]
  | WeakTermSigmaElim Sortal
                      [(Upsilon, a)]
                      a
                      a
  | WeakTermUniv UnivLevel
  | WeakTermRecurse Upsilon
                    a
  | WeakTermConstant Identifier
  | WeakTermHole Identifier

type WeakTerm = Cofree WeakTermF Identifier

$(deriveShow1 ''WeakTermF)

type SubstWeakTerm = [(Identifier, WeakTerm)]

varWeakTerm :: WeakTerm -> [Identifier]
varWeakTerm e = fst $ varAndHole e

varAndHole :: WeakTerm -> ([Identifier], [Identifier])
varAndHole (_ :< WeakTermVar s) = ([s], [])
varAndHole (_ :< WeakTermPi (x, tdom) tcod) = do
  let vs1 = varAndHole tdom
  let (vs21, vs22) = varAndHole tcod
  let vs2 = (filter (/= x) vs21, vs22)
  pairwiseConcat [vs1, vs2]
varAndHole (_ :< WeakTermPiIntro (x, _) e) = do
  let (vs1, vs2) = varAndHole e
  (filter (/= x) vs1, vs2)
varAndHole (_ :< WeakTermPiElim e1 e2) =
  pairwiseConcat [varAndHole e1, varAndHole e2]
varAndHole (_ :< WeakTermSigma xts) = varAndHoleSigma xts
varAndHole (_ :< WeakTermSigmaIntro es) = pairwiseConcat $ map varAndHole es
varAndHole (_ :< WeakTermSigmaElim xs e1 e2) = do
  let vs1 = varAndHole e1
  let (vs21, vs22) = varAndHole e2
  let vs2 = (filter (`notElem` xs) vs21, vs22)
  pairwiseConcat [vs1, vs2]
varAndHole (_ :< WeakTermEpsilon _) = ([], [])
varAndHole (_ :< WeakTermEpsilonIntro _) = ([], [])
varAndHole (_ :< WeakTermEpsilonElim e branchList) = do
  let vs1 = varAndHole e
  vss <- forM branchList $ \(_, body) -> return $ varAndHole body
  pairwiseConcat (vs1 : vss)
varAndHole (_ :< WeakTermConst _) = ([], [])
varAndHole (_ :< WeakTermUniv _) = ([], [])
varAndHole (_ :< WeakTermFix x e) = do
  let (vs1, vs2) = varAndHole e
  (filter (/= x) vs1, vs2)
varAndHole (_ :< WeakTermHole x) = ([], [x])

varAndHoleSigma :: [(Identifier, WeakTerm)] -> ([Identifier], [Identifier])
varAndHoleSigma [] = ([], [])
varAndHoleSigma ((x, t):xts) = do
  let vs1 = varAndHole t
  let (vs21, vs22) = varAndHoleSigma xts
  let vs2 = (filter (/= x) vs21, vs22)
  pairwiseConcat [vs1, vs2]

pairwiseConcat :: [([a], [b])] -> ([a], [b])
pairwiseConcat [] = ([], [])
pairwiseConcat ((xs, ys):rest) = do
  let (xs', ys') = pairwiseConcat rest
  (xs ++ xs', ys ++ ys')

substWeakTerm :: SubstWeakTerm -> WeakTerm -> WeakTerm
substWeakTerm sub (j :< WeakTermVar s) =
  fromMaybe (j :< WeakTermVar s) (lookup s sub)
substWeakTerm _ (j :< WeakTermConst t) = j :< WeakTermConst t
substWeakTerm sub (j :< WeakTermPi (s, tdom) tcod) = do
  let tdom' = substWeakTerm sub tdom
  let sub' = filter (\(x, _) -> x /= s) sub
  let tcod' = substWeakTerm sub' tcod
  j :< WeakTermPi (s, tdom') tcod'
substWeakTerm sub (j :< WeakTermPiIntro (s, tdom) body) = do
  let tdom' = substWeakTerm sub tdom
  let sub' = filter (\(x, _) -> x /= s) sub
  let body' = substWeakTerm sub' body
  j :< WeakTermPiIntro (s, tdom') body'
substWeakTerm sub (j :< WeakTermPiElim e1 e2) = do
  let e1' = substWeakTerm sub e1
  let e2' = substWeakTerm sub e2
  j :< WeakTermPiElim e1' e2'
substWeakTerm sub (j :< WeakTermSigma xts) =
  j :< WeakTermSigma (substWeakTermSigma sub xts)
substWeakTerm sub (j :< WeakTermSigmaIntro es) =
  j :< WeakTermSigmaIntro (map (substWeakTerm sub) es)
substWeakTerm sub (j :< WeakTermSigmaElim xs e1 e2) = do
  let e1' = substWeakTerm sub e1
  let sub' = filter (\(x, _) -> x `notElem` xs) sub
  let e2' = substWeakTerm sub' e2
  j :< WeakTermSigmaElim xs e1' e2'
substWeakTerm _ (j :< WeakTermEpsilon x) = j :< WeakTermEpsilon x
substWeakTerm _ (j :< WeakTermEpsilonIntro l) = j :< WeakTermEpsilonIntro l
substWeakTerm sub (j :< WeakTermEpsilonElim e branchList) = do
  let e' = substWeakTerm sub e
  let (labelList, es) = unzip branchList
  let es' = map (substWeakTerm sub) es
  j :< WeakTermEpsilonElim e' (zip labelList es')
substWeakTerm _ (j :< WeakTermUniv i) = j :< WeakTermUniv i
substWeakTerm sub (j :< WeakTermFix x e) = do
  let sub' = filter (\(y, _) -> x /= y) sub
  let e' = substWeakTerm sub' e
  j :< WeakTermFix x e'
substWeakTerm sub (j :< WeakTermHole s) =
  fromMaybe (j :< WeakTermHole s) (lookup s sub)

substWeakTermSigma ::
     SubstWeakTerm -> [(Identifier, WeakTerm)] -> [(Identifier, WeakTerm)]
substWeakTermSigma _ [] = []
substWeakTermSigma sub ((x, t):rest) = do
  let sub' = filter (\(y, _) -> y /= x) sub
  let xts = substWeakTermSigma sub' rest
  let t' = substWeakTerm sub t
  (x, t') : xts

isReducible :: WeakTerm -> Bool
isReducible (_ :< WeakTermVar _) = False
isReducible (_ :< WeakTermConst _) = False
isReducible (_ :< WeakTermPi (_, _) _) = False
isReducible (_ :< WeakTermPiIntro _ _) = False
isReducible (_ :< WeakTermPiElim (_ :< WeakTermPiIntro _ _) _) = True
isReducible (_ :< WeakTermPiElim e1 _) = isReducible e1
isReducible (_ :< WeakTermSigma _) = False
isReducible (_ :< WeakTermSigmaIntro es) = any isReducible es
isReducible (_ :< WeakTermSigmaElim _ (_ :< WeakTermSigmaIntro _) _) = True
isReducible (_ :< WeakTermSigmaElim _ e _) = isReducible e
isReducible (_ :< WeakTermEpsilon _) = False
isReducible (_ :< WeakTermEpsilonIntro _) = False
isReducible (_ :< WeakTermEpsilonElim (_ :< WeakTermEpsilonIntro _) _) = True
isReducible (_ :< WeakTermEpsilonElim e _) = isReducible e
isReducible (_ :< WeakTermUniv _) = False
isReducible (_ :< WeakTermFix _ _) = True
isReducible (_ :< WeakTermHole _) = False

toWeakTermPiIntroSeq ::
     WeakTerm -> (WeakTerm, [(Identifier, WeakTerm, Identifier)])
toWeakTermPiIntroSeq (meta :< WeakTermPiIntro (x, t) body) = do
  let (body', args) = toWeakTermPiIntroSeq body
  (body', (x, t, meta) : args)
toWeakTermPiIntroSeq t = (t, [])

fromWeakTermPiElimSeq :: (WeakTerm, [(Identifier, WeakTerm)]) -> WeakTerm
fromWeakTermPiElimSeq (term, []) = term
fromWeakTermPiElimSeq (term, (i, v):xs) =
  fromWeakTermPiElimSeq (i :< WeakTermPiElim term v, xs)

toWeakTermPiElimSeq :: WeakTerm -> (WeakTerm, [(Identifier, WeakTerm)])
toWeakTermPiElimSeq (i :< WeakTermPiElim e1 e2) = do
  let (fun, xs) = toWeakTermPiElimSeq e1
  (fun, xs ++ [(i, e2)])
toWeakTermPiElimSeq c = (c, [])
