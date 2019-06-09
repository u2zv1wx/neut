{-# LANGUAGE DeriveFunctor   #-}
{-# LANGUAGE TemplateHaskell #-}

module Data.Neut where

import           Control.Comonad.Cofree
import           Control.Monad          (forM)
import           Data.Maybe             (fromMaybe)
import           Text.Show.Deriving

import           Data.Basic

data NeutF a
  = NeutVar Identifier
  | NeutConst Identifier
  | NeutPi (Identifier, a)
           a
  | NeutPiIntro (Identifier, a)
                a
  | NeutPiElim a
               a
  | NeutSigma [(Identifier, a)]
  | NeutSigmaIntro [a]
  | NeutSigmaElim [Identifier]
                  a
                  a
  | NeutIndex Identifier
  | NeutIndexIntro Index
  | NeutIndexElim a
                  [(Index, a)]
  | NeutUniv UnivLevel
  | NeutMu Identifier
           a
  | NeutHole Identifier

type Neut = Cofree NeutF Identifier

$(deriveShow1 ''NeutF)

type SubstNeut = [(Identifier, Neut)]

varNeut :: Neut -> [Identifier]
varNeut e = fst $ varAndHole e

varAndHole :: Neut -> ([Identifier], [Identifier])
varAndHole (_ :< NeutVar s) = ([s], [])
varAndHole (_ :< NeutPi (x, tdom) tcod) = do
  let vs1 = varAndHole tdom
  let (vs21, vs22) = varAndHole tcod
  let vs2 = (filter (/= x) vs21, vs22)
  pairwiseConcat [vs1, vs2]
varAndHole (_ :< NeutPiIntro (x, _) e) = do
  let (vs1, vs2) = varAndHole e
  (filter (/= x) vs1, vs2)
varAndHole (_ :< NeutPiElim e1 e2) =
  pairwiseConcat [varAndHole e1, varAndHole e2]
varAndHole (_ :< NeutSigma xts) = varAndHoleSigma xts
varAndHole (_ :< NeutSigmaIntro es) = pairwiseConcat $ map varAndHole es
varAndHole (_ :< NeutSigmaElim xs e1 e2) = do
  let vs1 = varAndHole e1
  let (vs21, vs22) = varAndHole e2
  let vs2 = (filter (`notElem` xs) vs21, vs22)
  pairwiseConcat [vs1, vs2]
varAndHole (_ :< NeutIndex _) = ([], [])
varAndHole (_ :< NeutIndexIntro _) = ([], [])
varAndHole (_ :< NeutIndexElim e branchList) = do
  let vs1 = varAndHole e
  vss <- forM branchList $ \(_, body) -> return $ varAndHole body
  pairwiseConcat (vs1 : vss)
varAndHole (_ :< NeutConst _) = ([], [])
varAndHole (_ :< NeutUniv _) = ([], [])
varAndHole (_ :< NeutMu x e) = do
  let (vs1, vs2) = varAndHole e
  (filter (/= x) vs1, vs2)
varAndHole (_ :< NeutHole x) = ([], [x])

varAndHoleSigma :: [(Identifier, Neut)] -> ([Identifier], [Identifier])
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

substNeut :: SubstNeut -> Neut -> Neut
substNeut sub (j :< NeutVar s) = fromMaybe (j :< NeutVar s) (lookup s sub)
substNeut _ (j :< NeutConst t) = j :< NeutConst t
substNeut sub (j :< NeutPi (s, tdom) tcod) = do
  let tdom' = substNeut sub tdom
  let sub' = filter (\(x, _) -> x /= s) sub
  let tcod' = substNeut sub' tcod
  j :< NeutPi (s, tdom') tcod'
substNeut sub (j :< NeutPiIntro (s, tdom) body) = do
  let tdom' = substNeut sub tdom
  let sub' = filter (\(x, _) -> x /= s) sub
  let body' = substNeut sub' body
  j :< NeutPiIntro (s, tdom') body'
substNeut sub (j :< NeutPiElim e1 e2) = do
  let e1' = substNeut sub e1
  let e2' = substNeut sub e2
  j :< NeutPiElim e1' e2'
substNeut sub (j :< NeutSigma xts) = j :< NeutSigma (substNeutSigma sub xts)
substNeut sub (j :< NeutSigmaIntro es) =
  j :< NeutSigmaIntro (map (substNeut sub) es)
substNeut sub (j :< NeutSigmaElim xs e1 e2) = do
  let e1' = substNeut sub e1
  let sub' = filter (\(x, _) -> x `notElem` xs) sub
  let e2' = substNeut sub' e2
  j :< NeutSigmaElim xs e1' e2'
substNeut _ (j :< NeutIndex x) = j :< NeutIndex x
substNeut _ (j :< NeutIndexIntro l) = j :< NeutIndexIntro l
substNeut sub (j :< NeutIndexElim e branchList) = do
  let e' = substNeut sub e
  let (labelList, es) = unzip branchList
  let es' = map (substNeut sub) es
  j :< NeutIndexElim e' (zip labelList es')
substNeut _ (j :< NeutUniv i) = j :< NeutUniv i
substNeut sub (j :< NeutMu x e) = do
  let sub' = filter (\(y, _) -> x /= y) sub
  let e' = substNeut sub' e
  j :< NeutMu x e'
substNeut sub (j :< NeutHole s) = fromMaybe (j :< NeutHole s) (lookup s sub)

substNeutSigma :: SubstNeut -> [(Identifier, Neut)] -> [(Identifier, Neut)]
substNeutSigma _ [] = []
substNeutSigma sub ((x, t):rest) = do
  let sub' = filter (\(y, _) -> y /= x) sub
  let xts = substNeutSigma sub' rest
  let t' = substNeut sub t
  (x, t') : xts

isReducible :: Neut -> Bool
isReducible (_ :< NeutVar _) = False
isReducible (_ :< NeutConst _) = False
isReducible (_ :< NeutPi (_, _) _) = False
isReducible (_ :< NeutPiIntro _ _) = False
isReducible (_ :< NeutPiElim (_ :< NeutPiIntro _ _) _) = True
isReducible (_ :< NeutPiElim e1 _) = isReducible e1
isReducible (_ :< NeutSigma _) = False
isReducible (_ :< NeutSigmaIntro es) = any isReducible es
isReducible (_ :< NeutSigmaElim _ (_ :< NeutSigmaIntro _) _) = True
isReducible (_ :< NeutSigmaElim _ e _) = isReducible e
isReducible (_ :< NeutIndex _) = False
isReducible (_ :< NeutIndexIntro _) = False
isReducible (_ :< NeutIndexElim (_ :< NeutIndexIntro _) _) = True
isReducible (_ :< NeutIndexElim e _) = isReducible e
isReducible (_ :< NeutUniv _) = False
isReducible (_ :< NeutMu _ _) = True
isReducible (_ :< NeutHole _) = False

toNeutPiIntroSeq :: Neut -> (Neut, [(Identifier, Neut, Identifier)])
toNeutPiIntroSeq (meta :< NeutPiIntro (x, t) body) = do
  let (body', args) = toNeutPiIntroSeq body
  (body', (x, t, meta) : args)
toNeutPiIntroSeq t = (t, [])

fromNeutPiElimSeq :: (Neut, [(Identifier, Neut)]) -> Neut
fromNeutPiElimSeq (term, []) = term
fromNeutPiElimSeq (term, (i, v):xs) =
  fromNeutPiElimSeq (i :< NeutPiElim term v, xs)

toNeutPiElimSeq :: Neut -> (Neut, [(Identifier, Neut)])
toNeutPiElimSeq (i :< NeutPiElim e1 e2) = do
  let (fun, xs) = toNeutPiElimSeq e1
  (fun, xs ++ [(i, e2)])
toNeutPiElimSeq c = (c, [])
