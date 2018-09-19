module Infer
  ( check
  , unify
  ) where

import           Control.Monad
import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Control.Comonad.Cofree

import qualified Text.Show.Pretty           as Pr

import           Data
import           Data.Maybe

check :: Identifier -> Neut -> WithEnv ()
check main e = do
  t <- infer e
  insTypeEnv main t -- insert the type of main function
  env <- get
  sub <- unifyLoop (constraintEnv env) 0
  let tenv' = map (\(s, t) -> (s, subst sub t)) $ typeEnv env
  modify (\e -> e {typeEnv = tenv', constraintEnv = []})

infer :: Neut -> WithEnv Neut
infer (meta :< NeutVar s) = do
  t <- lookupTypeEnv' s
  returnMeta meta t
infer (meta :< NeutPi (s, tdom) tcod) = inferBinder meta s tdom tcod
infer (meta :< NeutPiIntro (s, tdom) e) = do
  insTypeEnv s tdom
  udom <- infer tdom
  tcod <- infer e
  ucod <- infer tcod
  insConstraintEnv udom ucod
  wrapTypeWithUniv udom (NeutPi (s, tdom) tcod) >>= returnMeta meta
infer (meta :< NeutPiElim e1 e2) = do
  tPi <- infer e1 -- forall (x : tdom). tcod
  tdom <- infer e2
  udom <- infer tdom
  tcod <- newHole
  ucod <- infer tcod
  insConstraintEnv udom ucod
  x <- newNameOfType tdom
  typeMeta2 <- newNameWith "meta"
  insTypeEnv typeMeta2 udom
  insConstraintEnv tPi (typeMeta2 :< NeutPi (x, tdom) tcod) -- t1 == forall (x : tdom). tcod
  returnMeta meta $ explicitSubst tcod [(x, e2)]
infer (meta :< NeutSigma (s, tdom) tcod) = inferBinder meta s tdom tcod
infer (meta :< NeutSigmaIntro e1 e2) = do
  t1 <- infer e1 -- A
  t2 <- infer e2 -- B {x := e1}
  u1 <- infer t1
  u2 <- infer t2
  insConstraintEnv u1 u2
  t2nosub <- newHole -- B
  x <- newNameOfType t1
  let t2sub = explicitSubst t2nosub [(x, e1)]
  insConstraintEnv t2 t2sub
  wrapTypeWithUniv u1 (NeutSigma (x, t1) t2nosub) >>= returnMeta meta -- Sigma (x : A). B
infer (meta :< NeutSigmaElim e1 (x, y) e2) = do
  t1 <- infer e1
  u1 <- infer t1
  tx <- newHole
  ux <- infer tx
  ty <- newHole
  uy <- infer ty
  t2 <- infer e2
  u2 <- infer t2
  insTypeEnv x tx
  insTypeEnv y ty
  insConstraintEnv u1 u2
  insConstraintEnv u1 ux
  insConstraintEnv ux uy
  sigmaType <- wrapType $ NeutSigma (x, tx) ty
  insConstraintEnv t1 sigmaType
  z <- newNameOfType t1
  pair <- constructPair x y
  resultHole <- newHole
  insConstraintEnv t2 $ explicitSubst resultHole [(z, pair)]
  returnMeta meta $ explicitSubst resultHole [(z, e1)]
infer (meta :< NeutMu s e) = do
  trec <- newHole
  insTypeEnv s trec
  te <- infer e
  insConstraintEnv te trec
  returnMeta meta te
infer (meta :< NeutTop) = do
  hole <- newName
  wrap (NeutUniv (UnivLevelHole hole)) >>= returnMeta meta
infer (meta :< NeutTopIntro) = wrapType NeutTop >>= returnMeta meta
infer (meta :< NeutUniv l) =
  wrap (NeutUniv (UnivLevelNext l)) >>= returnMeta meta
infer (meta :< NeutHole _) = do
  hole <- newName
  wrap (NeutUniv (UnivLevelHole hole)) >>= returnMeta meta
infer (_ :< NeutSubst e _) = infer e

inferBinder :: Identifier -> Identifier -> Neut -> Neut -> WithEnv Neut
inferBinder meta s tdom tcod = do
  udom <- infer tdom
  insTypeEnv s tdom
  ucod <- infer tcod
  insConstraintEnv udom ucod
  returnMeta meta udom

constructPair :: Identifier -> Identifier -> WithEnv Neut
constructPair x y = do
  eMeta <- newName
  xMeta <- newName
  yMeta <- newName
  let pair = eMeta :< NeutSigmaIntro (xMeta :< NeutVar x) (yMeta :< NeutVar y)
  _ <- infer pair
  return pair

newNameOfType :: Neut -> WithEnv Identifier
newNameOfType t = do
  i <- newName
  insTypeEnv i t
  return i

explicitSubst :: Neut -> [(Identifier, Neut)] -> Neut
explicitSubst e1 sub = "" :< NeutSubst e1 sub

newHole :: WithEnv Neut
newHole = do
  i <- newName
  wrapType $ NeutHole i

returnMeta :: Identifier -> Neut -> WithEnv Neut
returnMeta meta t = do
  insTypeEnv meta t
  return t

type Constraint = [(Neut, Neut)]

unifyLoop :: Constraint -> Int -> WithEnv Subst
unifyLoop [] _ = return []
unifyLoop ((e1, e2):cs) loopCount = do
  (tmpSubst, tmpConstraint) <- unify ((reduce e1, reduce e2) : cs)
  case (tmpSubst, tmpConstraint) of
    (s, []) -> return s
    (s, (e1', e2'):cs') -> do
      let loopCount' = nextLoopCount (length cs) (length cs') loopCount
      if didFinishLoop (length cs') loopCount'
        then unificationFailed (reduce e1) (reduce e2) cs'
        else do
          s' <- unifyLoop (cs' ++ [(e1', e2')]) loopCount'
          return (s ++ s')

unificationFailed :: Neut -> Neut -> Constraint -> WithEnv Subst
unificationFailed e1 e2 cs =
  lift $
  throwE $
  "unification failed for\n" ++
  Pr.ppShow e1 ++
  "\nand\n" ++ Pr.ppShow e2 ++ "\nwith constraints:\n" ++ Pr.ppShow cs

nextLoopCount :: Int -> Int -> Int -> Int
nextLoopCount i j loopCount = do
  let lenOld = i + 1
  let lenNew = j + 1
  if lenOld <= lenNew
    then loopCount + 1
    else 0

didFinishLoop :: Int -> Int -> Bool
didFinishLoop j loopCount' = loopCount' >= j + 2

unify :: Constraint -> WithEnv (Subst, Constraint)
unify [] = return ([], [])
unify ((_ :< NeutHole s, t2):cs) = do
  (sub, cs') <- unify (sConstraint [(s, t2)] cs)
  return (compose sub [(s, t2)], cs')
unify ((t1, _ :< NeutHole s):cs) = do
  (sub, cs') <- unify (sConstraint [(s, t1)] cs)
  return (compose sub [(s, t1)], cs')
unify ((_ :< NeutVar s1, _ :< NeutVar s2):cs)
  | s1 == s2 = unify cs
unify ((_ :< NeutPi (_, tdom1) tcod1, _ :< NeutPi (_, tdom2) tcod2):cs) =
  unify $ (tdom1, tdom2) : (tcod1, tcod2) : cs
unify ((_ :< NeutSigma (_, tdom1) tcod1, _ :< NeutSigma (_, tdom2) tcod2):cs) =
  unify $ (tdom1, tdom2) : (tcod1, tcod2) : cs
unify ((_ :< NeutTop, _ :< NeutTop):cs) = unify cs
unify ((_ :< NeutUniv i, _ :< NeutUniv j):cs) = do
  insUnivConstraintEnv i j
  unify cs
unify cs = return ([], cs)

sConstraint :: Subst -> Constraint -> Constraint
sConstraint s = map (\(t1, t2) -> (subst s t1, subst s t2))
