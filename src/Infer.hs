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
  sub <- unify (constraintEnv env)
  let tenv' = map (\(s, t) -> (s, subst sub t)) $ typeEnv env
  modify (\e -> e {typeEnv = tenv', constraintEnv = []})

infer :: Neut -> WithEnv WeakType
infer (meta :< NeutVar s) = do
  t <- lookupTypeEnv' s
  returnMeta meta t
infer (meta :< NeutArrowIntro (s, tdom) e) = do
  insTypeEnv s tdom
  te <- infer e
  returnMeta meta $ WeakTypeArrow tdom te
infer (meta :< NeutArrowElim e1 e2) = do
  t1 <- infer e1 -- forall (x : tdom). tcod
  tdom <- infer e2
  tcod <- newHole
  insConstraintEnv t1 (WeakTypeArrow tdom tcod) -- t1 == forall (x : tdom). tcod
  returnMeta meta tcod
infer (meta :< NeutForallIntro x e) = do
  te <- infer e
  returnMeta meta $ WeakTypeForall x te
infer (meta :< NeutForallElim e t) = do
  te <- infer e -- forall (x : tdom). tcod
  returnMeta meta $ WeakTypeApp te t
infer (meta :< NeutPiIntro xs) = undefined
infer (meta :< NeutPiElim e1 e2) = undefined
infer (meta :< NeutProductIntro e1 e2) = do
  t1 <- infer e1
  t2 <- infer e2
  returnMeta meta $ WeakTypeProduct t1 t2
infer (meta :< NeutProductElim e1 (x, y) e2) = do
  t1 <- infer e1
  xHole <- newHole
  insTypeEnv x xHole
  yHole <- newHole
  insTypeEnv y yHole
  insConstraintEnv t1 $ WeakTypeProduct xHole yHole
  t2 <- infer e2
  returnMeta meta t2
infer (meta :< NeutExistsIntro x e) = do
  undefined
infer (meta :< NeutExistsElim e1 (x, y) e2) = do
  undefined
infer (meta :< NeutSigmaIntro x e) = do
  undefined
infer (meta :< NeutSigmaElim e clauseList) = do
  undefined
infer (meta :< NeutMu s e) = do
  trec <- newHole
  insTypeEnv s trec
  te <- infer e
  insConstraintEnv te trec
  returnMeta meta te
infer (meta :< NeutTopIntro) = returnMeta meta WeakTypeTop

newHole :: WithEnv WeakType
newHole = WeakTypeHole <$> newName

returnMeta :: Identifier -> WeakType -> WithEnv WeakType
returnMeta meta t = do
  insTypeEnv meta t
  return t

type Constraint = [(WeakType, WeakType)]

unify :: Constraint -> WithEnv Subst
unify [] = return []
unify ((WeakTypeHole s, t2):cs) = do
  sub <- unify (sConstraint [(s, t2)] cs)
  return $ compose sub [(s, t2)]
unify ((t1, WeakTypeHole s):cs) = do
  sub <- unify (sConstraint [(s, t1)] cs)
  return $ compose sub [(s, t1)]
unify ((WeakTypeVar s1, WeakTypeVar s2):cs)
  | s1 == s2 = unify cs
unify ((WeakTypeForall x tcod1, WeakTypeForall y tcod2):cs) = undefined
  -- unify $ (tdom1, tdom2) : (tcod1, tcod2) : cs
unify ((WeakTypeExists x tcod1, WeakTypeExists y tcod2):cs) = undefined
  -- unify $ (tdom1, tdom2) : (tcod1, tcod2) : cs
unify ((WeakTypeTop, WeakTypeTop):cs) = unify cs
unify cs@((e1, e2):_) =
  lift $
  throwE $
  "unification failed for\n" ++
  Pr.ppShow e1 ++
  "\nand\n" ++ Pr.ppShow e2 ++ "\nwith constraints:\n" ++ Pr.ppShow cs

sConstraint :: Subst -> Constraint -> Constraint
sConstraint s = map (\(t1, t2) -> (subst s t1, subst s t2))
