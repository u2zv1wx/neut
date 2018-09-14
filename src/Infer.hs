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
  sub <- unify $ constraintEnv env
  let tenv' = map (\(s, t) -> (s, subst sub t)) $ typeEnv env
  modify (\e -> e {typeEnv = tenv', constraintEnv = []})

infer :: Neut -> WithEnv Neut
infer (meta :< NeutVar s) = do
  mt <- lookupTypeEnv s
  case mt of
    Just t -> do
      insTypeEnv meta t
      return t
    _ -> lift $ throwE $ "undefined variable: " ++ s
infer (meta :< NeutForall (s, tdom) tcod) = do
  udom <- infer tdom
  wrapUniv NeutUniv >>= \u -> insConstraintEnv udom u
  insTypeEnv s tdom
  ucod <- infer tcod
  wrapUniv NeutUniv >>= \u -> insConstraintEnv ucod u
  return $ meta :< NeutUniv
infer (meta :< NeutLam (s, tdom) e) = do
  insTypeEnv s tdom
  te <- infer e
  typeMeta <- newNameWith "meta"
  let result = typeMeta :< NeutForall (s, tdom) te
  insTypeEnv meta result
  return result
infer (meta :< NeutApp e v) = do
  te <- infer e
  tdom <- infer v
  i <- newName
  tcod <- wrapType $ NeutHole i
  j <- newName
  insTypeEnv j tdom
  typeMeta2 <- newNameWith "meta"
  insConstraintEnv te (typeMeta2 :< NeutForall (j, tdom) tcod)
  result <- bindWithLet j tdom v tcod -- let x := v in tcod
  insTypeEnv meta result
  return result
infer (meta :< NeutExists (s, tdom) tcod) = do
  udom <- infer tdom
  wrapUniv NeutUniv >>= \u -> insConstraintEnv udom u
  insTypeEnv s tdom
  ucod <- infer tcod
  wrapUniv NeutUniv >>= \u -> insConstraintEnv ucod u
  return $ meta :< NeutUniv
infer (meta :< NeutPair e1 e2) = do
  x <- newName
  t1 <- infer e1
  insTypeEnv x t1
  t2 <- infer e2
  j <- NeutHole <$> newName >>= wrapType
  hole <- bindWithLet x t1 e1 j -- typeof(e2) == B {x := e1} == let x := e1 in HOLE
  insConstraintEnv t2 hole
  result <- wrapType $ NeutExists (x, t1) hole
  insTypeEnv meta result
  return result
infer (meta :< NeutCase e1 (x, y) e2) = do
  t1 <- infer e1
  xHole <- newNameWith x >>= \x -> wrapType (NeutHole x)
  yHole <- newNameWith y >>= \y -> wrapType (NeutHole y)
  z <- newName
  eMeta <- newName
  xMeta <- newName
  yMeta <- newName
  let pair = eMeta :< NeutPair (xMeta :< NeutVar x) (yMeta :< NeutVar y)
  yHole' <- bindWithLet z t1 pair yHole
  sigmaType <- wrapType $ NeutExists (x, xHole) yHole
  insConstraintEnv t1 sigmaType
  t2 <- infer e2
  insConstraintEnv yHole' t2
  result <- bindWithLet z t1 e1 yHole
  insTypeEnv meta result
  return result
infer (meta :< NeutMu s e) = do
  j <- newName
  trec <- wrapType $ NeutHole j
  insTypeEnv s trec
  te <- infer e
  insConstraintEnv te trec
  insTypeEnv meta te
  return te
infer (meta :< NeutTop) = do
  u <- wrapUniv NeutUniv
  insTypeEnv meta u
  return u
infer (meta :< NeutUnit) = do
  t <- wrapType NeutTop
  insTypeEnv meta t
  return t
infer (meta :< NeutBottom) = do
  u <- wrapUniv NeutUniv
  insTypeEnv meta u
  return u
infer (meta :< NeutAbort e) = do
  t <- infer e
  t' <- wrapType NeutBottom
  insConstraintEnv t t'
  i <- newName
  result <- wrapType $ NeutHole i
  insTypeEnv meta result
  return result
infer (_ :< NeutUniv) = error "the level of type universe hierarchy is upto 2"
infer (meta :< NeutHole _) = do
  result <- wrapUniv NeutUniv
  insTypeEnv meta result
  return result

wrapUniv :: NeutF Neut -> WithEnv Neut
wrapUniv a = do
  meta <- newNameWith "meta"
  return $ meta :< a

wrapType :: NeutF Neut -> WithEnv Neut
wrapType t = do
  meta <- newNameWith "meta"
  u <- wrapUniv NeutUniv
  insTypeEnv meta u
  return $ meta :< t

-- bindWithLet x tdom e1 e2 ~> let x : tdom := e1 in e2
bindWithLet :: Identifier -> Neut -> Neut -> Neut -> WithEnv Neut
bindWithLet x tdom e1 e2 = do
  i <- newName
  j <- newName
  return $ j :< NeutApp (i :< NeutLam (x, tdom) e2) e1

type Constraint = [(Neut, Neut)]

unify :: Constraint -> WithEnv Subst
unify [] = return []
unify ((_ :< NeutHole s, t2):cs) = do
  sub <- unify (sConstraint [(s, t2)] cs)
  return $ compose sub [(s, t2)]
unify ((t1, _ :< NeutHole s):cs) = do
  sub <- unify (sConstraint [(s, t1)] cs)
  return $ compose sub [(s, t1)]
unify ((_ :< NeutVar s1, _ :< NeutVar s2):cs)
  | s1 == s2 = unify cs
unify ((_ :< NeutForall (_, tdom1) tcod1, _ :< NeutForall (_, tdom2) tcod2):cs) =
  unify $ (tdom1, tdom2) : (tcod1, tcod2) : cs
unify ((_ :< NeutExists (_, tdom1) tcod1, _ :< NeutExists (_, tdom2) tcod2):cs) =
  unify $ (tdom1, tdom2) : (tcod1, tcod2) : cs
unify ((_ :< NeutTop, _ :< NeutTop):cs) = unify cs
unify ((_ :< NeutBottom, _ :< NeutBottom):cs) = unify cs
unify ((_ :< NeutUniv, _ :< NeutUniv):cs) = unify cs
unify ((t1, t2):_) =
  lift $
  throwE $
  "unification failed for:\n" ++ Pr.ppShow t1 ++ "\nand:\n" ++ Pr.ppShow t2

sConstraint :: Subst -> Constraint -> Constraint
sConstraint s = map (\(t1, t2) -> (subst s t1, subst s t2))
