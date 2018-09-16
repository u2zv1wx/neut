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
infer (meta :< NeutPi (s, tdom) tcod) = do
  mustBeType tdom
  insTypeEnv s tdom
  mustBeType tcod
  return $ meta :< NeutUniv
infer (meta :< NeutPiIntro (s, tdom) e) = do
  mustBeType tdom
  insTypeEnv s tdom
  te <- infer e
  wrapType (NeutPi (s, tdom) te) >>= returnMeta meta
infer (meta :< NeutPiElim e1 e2) = do
  t1 <- infer e1 -- forall (x : tdom). tcod
  tdom <- infer e2
  tcod <- newHole
  x <- newNameOfType tdom
  typeMeta2 <- newNameWith "meta"
  insConstraintEnv t1 (typeMeta2 :< NeutPi (x, tdom) tcod) -- t1 == forall (x : tdom). tcod
  bindWithLet' x e2 tcod >>= returnMeta meta -- tcod {x := e2}
infer (meta :< NeutSigma (s, tdom) tcod) = do
  mustBeType tdom
  insTypeEnv s tdom
  mustBeType tcod
  return $ meta :< NeutUniv
infer (meta :< NeutSigmaIntro e1 e2) = do
  t1 <- infer e1 -- A
  x <- newNameOfType t1
  t2 <- infer e2 -- B {x := e1}
  t2nosub <- newHole -- B
  t2sub <- bindWithLet' x e1 t2nosub -- B {x := e1}
  insConstraintEnv t2 t2sub
  wrapType (NeutSigma (x, t1) t2nosub) >>= returnMeta meta -- Sigma (x : A). B
infer (meta :< NeutSigmaElim e1 (x, y) e2) = do
  t1 <- infer e1
  xHole <- newHole
  insTypeEnv x xHole
  yHole <- newHole
  insTypeEnv y yHole
  sigmaType <- wrapType $ NeutSigma (x, xHole) yHole
  insConstraintEnv t1 sigmaType -- t1 == Sigma (x : A). B
  z <- newNameOfType t1
  pair <- constructPair x y
  resultHole <- newHole
  resultType <- bindWithLet' z pair resultHole -- C {z := (x, y)}
  resultType' <- bindWithLet' z e1 resultHole -- C {z := e1}
  t2 <- infer e2
  insConstraintEnv resultType t2
  returnMeta meta resultType'
infer (meta :< NeutMu s e) = do
  trec <- newHole
  insTypeEnv s trec
  te <- infer e
  insConstraintEnv te trec
  returnMeta meta te
infer (meta :< NeutTop) = wrap NeutUniv >>= returnMeta meta
infer (meta :< NeutTopIntro) = wrapType NeutTop >>= returnMeta meta
infer (_ :< NeutUniv) = error "the level of type universe hierarchy is upto 2"
infer (meta :< NeutHole _) = wrap NeutUniv >>= returnMeta meta

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

mustBeType :: Neut -> WithEnv ()
mustBeType t = do
  t' <- infer t
  wrap NeutUniv >>= \u -> insConstraintEnv t' u

bindWithLet' :: Identifier -> Neut -> Neut -> WithEnv Neut
bindWithLet' x e1 e2 = do
  e <- bindWithLet x e1 e2
  infer e >> return e

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
unifyLoop ((e1, e2):cs) loopCount =
  case unify ((reduce e1, reduce e2) : cs) of
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

unify :: Constraint -> (Subst, Constraint)
unify [] = ([], [])
unify ((_ :< NeutHole s, t2):cs) = do
  let (sub, cs') = unify (sConstraint [(s, t2)] cs)
  (compose sub [(s, t2)], cs')
unify ((t1, _ :< NeutHole s):cs) = do
  let (sub, cs') = unify (sConstraint [(s, t1)] cs)
  (compose sub [(s, t1)], cs')
unify ((_ :< NeutVar s1, _ :< NeutVar s2):cs)
  | s1 == s2 = unify cs
unify ((_ :< NeutPi (_, tdom1) tcod1, _ :< NeutPi (_, tdom2) tcod2):cs) =
  unify $ (tdom1, tdom2) : (tcod1, tcod2) : cs
unify ((_ :< NeutSigma (_, tdom1) tcod1, _ :< NeutSigma (_, tdom2) tcod2):cs) =
  unify $ (tdom1, tdom2) : (tcod1, tcod2) : cs
unify ((_ :< NeutTop, _ :< NeutTop):cs) = unify cs
unify ((_ :< NeutUniv, _ :< NeutUniv):cs) = unify cs
unify cs = ([], cs)

sConstraint :: Subst -> Constraint -> Constraint
sConstraint s = map (\(t1, t2) -> (subst s t1, subst s t2))
