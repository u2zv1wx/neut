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
  = WeakTermUniv UnivLevel
  | WeakTermUpsilon Upsilon
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
  | WeakTermRec (Upsilon, a)
                a
  | WeakTermConst Identifier
  | WeakTermHole Identifier

type WeakTerm = Cofree WeakTermF Identifier

$(deriveShow1 ''WeakTermF)

type SubstWeakTerm = [(Identifier, WeakTerm)]

varWeakTerm :: WeakTerm -> [Identifier]
varWeakTerm e = fst $ varAndHole e

varAndHole :: WeakTerm -> ([Identifier], [Identifier])
varAndHole (_ :< WeakTermUniv _) = ([], [])
varAndHole (_ :< WeakTermUpsilon (s, x)) = do
  let (xs, hs) = varAndHoleSortal s
  (x : xs, hs)
varAndHole (_ :< WeakTermEpsilon _) = ([], [])
varAndHole (_ :< WeakTermEpsilonIntro _) = ([], [])
varAndHole (_ :< WeakTermEpsilonElim e branchList) = do
  let vs1 = varAndHole e
  vss <- forM branchList $ \(_, body) -> return $ varAndHole body
  pairwiseConcat (vs1 : vss)
varAndHole (_ :< WeakTermPi s uts) = do
  let (xs1, hs1) = varAndHoleSortal s
  let (xs2, hs2) = varAndHoleBindings uts []
  (xs1 ++ xs2, hs1 ++ hs2)
varAndHole (_ :< WeakTermPiIntro s uts e) = do
  let (xs1, hs1) = varAndHoleSortal s
  let (xs2, hs2) = varAndHoleBindings uts [e]
  (xs1 ++ xs2, hs1 ++ hs2)
varAndHole (_ :< WeakTermPiElim s e es) =
  pairwiseConcat (varAndHoleSortal s : varAndHole e : map varAndHole es)
varAndHole (_ :< WeakTermSigma s uts) =
  pairwiseConcat [varAndHoleSortal s, varAndHoleBindings uts []]
varAndHole (_ :< WeakTermSigmaIntro s es) =
  pairwiseConcat $ varAndHoleSortal s : map varAndHole es
varAndHole (_ :< WeakTermSigmaElim s us e1 e2) =
  pairwiseConcat [varAndHole e1, varAndHoleSortal s, varAndHoleBindings us [e2]]
varAndHole (_ :< WeakTermRec ut e) = varAndHoleBindings [ut] [e]
varAndHole (_ :< WeakTermConst _) = ([], [])
varAndHole (_ :< WeakTermHole x) = ([], [x])

varAndHoleSortal :: Sortal -> ([Identifier], [Identifier])
varAndHoleSortal SortalPrimitive = ([], [])
varAndHoleSortal (SortalTerm e)  = varAndHole e

varAndHoleBindings ::
     [(Upsilon, WeakTerm)] -> [WeakTerm] -> ([Identifier], [Identifier])
varAndHoleBindings [] es = pairwiseConcat $ map varAndHole es
varAndHoleBindings (((s, x), t):uts) es = do
  let (xs1, hs1) = varAndHoleSortal s
  let (xs2, hs2) = varAndHole t
  let (xs3, hs3) = varAndHoleBindings uts es
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
substWeakTerm sub (j :< WeakTermEpsilonElim e branchList) = do
  let e' = substWeakTerm sub e
  let (caseList, es) = unzip branchList
  let es' = map (substWeakTerm sub) es
  j :< WeakTermEpsilonElim e' (zip caseList es')
substWeakTerm sub (j :< WeakTermPi s uts) = do
  let s' = substWeakTermSortal sub s
  let uts' = substWeakTermBindings sub uts
  j :< WeakTermPi s' uts'
substWeakTerm sub (j :< WeakTermPiIntro s uts body) = do
  let s' = substWeakTermSortal sub s
  let (uts', body') = substWeakTermBindingsWithBody sub uts body
  j :< WeakTermPiIntro s' uts' body'
substWeakTerm sub (j :< WeakTermPiElim s e es) = do
  let s' = substWeakTermSortal sub s
  let e' = substWeakTerm sub e
  let es' = map (substWeakTerm sub) es
  j :< WeakTermPiElim s' e' es'
substWeakTerm sub (j :< WeakTermSigma s uts) = do
  let s' = substWeakTermSortal sub s
  let uts' = substWeakTermBindings sub uts
  j :< WeakTermSigma s' uts'
substWeakTerm sub (j :< WeakTermSigmaIntro s es) = do
  let s' = substWeakTermSortal sub s
  let es' = map (substWeakTerm sub) es
  j :< WeakTermSigmaIntro s' es'
substWeakTerm sub (j :< WeakTermSigmaElim s uts e1 e2) = do
  let s' = substWeakTermSortal sub s
  let e1' = substWeakTerm sub e1
  let (uts', e2') = substWeakTermBindingsWithBody sub uts e2
  j :< WeakTermSigmaElim s' uts' e1' e2'
substWeakTerm sub (j :< WeakTermRec ((s, x), t) e) = do
  let s' = substWeakTermSortal sub s
  let t' = substWeakTerm sub t
  let e' = substWeakTerm (filter (\(k, _) -> k /= x) sub) e
  j :< WeakTermRec ((s', x), t') e'
substWeakTerm _ (j :< WeakTermConst t) = j :< WeakTermConst t
substWeakTerm sub (j :< WeakTermHole s) =
  fromMaybe (j :< WeakTermHole s) (lookup s sub)

substWeakTermBindings ::
     SubstWeakTerm -> [(Upsilon, WeakTerm)] -> [(Upsilon, WeakTerm)]
substWeakTermBindings _ [] = []
substWeakTermBindings sub (((s, x), t):uts) = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let uts' = substWeakTermBindings sub' uts
  ((substWeakTermSortal sub s, x), substWeakTerm sub t) : uts'

substWeakTermBindingsWithBody ::
     SubstWeakTerm
  -> [(Upsilon, WeakTerm)]
  -> WeakTerm
  -> ([(Upsilon, WeakTerm)], WeakTerm)
substWeakTermBindingsWithBody sub [] e = ([], substWeakTerm sub e)
substWeakTermBindingsWithBody sub (((s, x), t):uts) e = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let (uts', e') = substWeakTermBindingsWithBody sub' uts e
  (((substWeakTermSortal sub s, x), substWeakTerm sub t) : uts', e')

substWeakTermSortal :: SubstWeakTerm -> Sortal -> Sortal
substWeakTermSortal _ SortalPrimitive  = SortalPrimitive
substWeakTermSortal sub (SortalTerm e) = SortalTerm $ substWeakTerm sub e

isReducible :: WeakTerm -> Bool
isReducible = undefined

-- isReducible (_ :< WeakTermUpsilon _) = False
-- isReducible (_ :< WeakTermConst _) = False
-- isReducible (_ :< WeakTermPi (_, _) _) = False
-- isReducible (_ :< WeakTermPiIntro _ _) = False
-- isReducible (_ :< WeakTermPiElim (_ :< WeakTermPiIntro _ _) _) = True
-- isReducible (_ :< WeakTermPiElim e1 _) = isReducible e1
-- isReducible (_ :< WeakTermSigma _) = False
-- isReducible (_ :< WeakTermSigmaIntro es) = any isReducible es
-- isReducible (_ :< WeakTermSigmaElim _ (_ :< WeakTermSigmaIntro _) _) = True
-- isReducible (_ :< WeakTermSigmaElim _ e _) = isReducible e
-- isReducible (_ :< WeakTermEpsilon _) = False
-- isReducible (_ :< WeakTermEpsilonIntro _) = False
-- isReducible (_ :< WeakTermEpsilonElim (_ :< WeakTermEpsilonIntro _) _) = True
-- isReducible (_ :< WeakTermEpsilonElim e _) = isReducible e
-- isReducible (_ :< WeakTermUniv _) = False
-- isReducible (_ :< WeakTermRec _ _) = True
-- isReducible (_ :< WeakTermHole _) = False
toWeakTermPiIntroSeq ::
     WeakTerm -> (WeakTerm, [(Identifier, WeakTerm, Identifier)])
toWeakTermPiIntroSeq = undefined

-- toWeakTermPiIntroSeq (meta :< WeakTermPiIntro (x, t) body) = do
--   let (body', args) = toWeakTermPiIntroSeq body
--   (body', (x, t, meta) : args)
-- toWeakTermPiIntroSeq t = (t, [])
fromWeakTermPiElimSeq :: (WeakTerm, [(Identifier, WeakTerm)]) -> WeakTerm
fromWeakTermPiElimSeq (term, [])        = term
fromWeakTermPiElimSeq (term, (i, v):xs) = undefined
  -- fromWeakTermPiElimSeq (i :< WeakTermPiElim term v, xs)

toWeakTermPiElimSeq :: WeakTerm -> (WeakTerm, [(Identifier, WeakTerm)])
toWeakTermPiElimSeq = undefined
-- toWeakTermPiElimSeq (i :< WeakTermPiElim e1 e2) = do
--   let (fun, xs) = toWeakTermPiElimSeq e1
--   (fun, xs ++ [(i, e2)])
-- toWeakTermPiElimSeq c = (c, [])
