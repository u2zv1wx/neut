module Elaborate
  ( elaborate
  ) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Trans.Except

import Control.Comonad.Cofree

import qualified Text.Show.Pretty as Pr

import Data
import Exhaust
import Reduce
import Util

import Elaborate.Analyze
import Elaborate.Infer
import Elaborate.Synthesize

import Data.List

import Data.Maybe

import qualified Data.PQueue.Min as Q

-- Given a term `e` and its name `main`, this function
--   (1) traces `e` using `infer e`, collecting type constraints,
--   (1.1) if a variable occurs more than twice in `e`, constrain it to have box type,
--   (2) updates typeEnv for `main` by the result of `infer e`,
--   (3) analyze the constraints, solving easy ones,
--   (4) synthesize these analyzed constraints, solving as many solutions as possible,
--   (5) elaborate the given term using the result of synthesis.
-- The inference algorithm in this module is based on L. de Moura, J. Avigad,
-- S. Kong, and C. Roux. "Elaboration in Dependent Type Theory", arxiv,
-- https://arxiv.org/abs/1505.04324, 2015.
elaborate :: Identifier -> Neut -> WithEnv ()
elaborate main e = do
  t <- infer [] e
  insTypeEnv main t
  boxConstraint [] $ nonLinear e
  -- Kantian type-inference ;)
  gets constraintEnv >>= analyze
  gets constraintQueue >>= synthesize
  -- update the type environment by resulting substitution
  sub <- gets substitution
  tenv <- gets typeEnv
  tenv' <-
    forM tenv $ \(i, t) -> do
      t' <- reduce $ subst sub t
      return (i, t')
  modify (\e -> e {typeEnv = tenv'})
  checkNumConstraint
  -- use the resulting substitution to elaborate `e`.
  nonRecReduce e >>= exhaust >>= elaborate' >>= insTermEnv main

-- In short: numbers must have one of the number types. We firstly generate constraints
-- assuming that `1`, `1.2321`, etc. have arbitrary types. After the inference finished,
-- we check if all of them have one of the number types, such as i32, f64, etc.
checkNumConstraint :: WithEnv ()
checkNumConstraint = do
  env <- get
  forM_ (numConstraintEnv env) $ \x -> do
    t <- lookupTypeEnv' x
    case t of
      _ :< NeutIndex "i1" -> return ()
      _ :< NeutIndex "i2" -> return ()
      _ :< NeutIndex "i4" -> return ()
      _ :< NeutIndex "i8" -> return ()
      _ :< NeutIndex "i16" -> return ()
      _ :< NeutIndex "i32" -> return ()
      _ :< NeutIndex "i64" -> return ()
      _ :< NeutIndex "u1" -> return ()
      _ :< NeutIndex "u2" -> return ()
      _ :< NeutIndex "u4" -> return ()
      _ :< NeutIndex "u8" -> return ()
      _ :< NeutIndex "u16" -> return ()
      _ :< NeutIndex "u32" -> return ()
      _ :< NeutIndex "u64" -> return ()
      _ :< NeutIndex "f16" -> return ()
      _ :< NeutIndex "f32" -> return ()
      _ :< NeutIndex "f64" -> return ()
      t ->
        lift $
        throwE $
        "the type of " ++
        x ++ " is supposed to be a number, but is " ++ Pr.ppShow t

elaborate' :: Neut -> WithEnv Term
elaborate' (_ :< NeutVar s) = TermVar <$> lookupNameEnv s
elaborate' (_ :< NeutPi (s, tdom) tcod) = do
  tdom' <- elaborate' tdom
  tcod' <- elaborate' tcod
  return $ TermPi (s, tdom') tcod'
elaborate' (_ :< NeutPiIntro (s, _) e) = do
  e' <- elaborate' e
  return $ TermPiIntro s e'
elaborate' (_ :< NeutPiElim e v) = do
  e' <- elaborate' e
  v' <- elaborate' v
  return $ TermPiElim e' v'
elaborate' (_ :< NeutSigma xts tcod) = do
  let (xs, ts) = unzip xts
  ts' <- mapM elaborate' ts
  tcod' <- elaborate' tcod
  return $ TermSigma (zip xs ts') tcod'
elaborate' (i :< NeutSigmaIntro es) = do
  t <- lookupTypeEnv' i
  es' <- mapM elaborate' es
  return $ TermSigmaIntro (sigmaSize t) es'
elaborate' (_ :< NeutSigmaElim e1@(i :< _) xs e2) = do
  t <- lookupTypeEnv' i
  e1' <- elaborate' e1
  e2' <- elaborate' e2
  return $ TermSigmaElim (sigmaSize t) e1' xs e2'
elaborate' (_ :< NeutBox t) = do
  t' <- elaborate' t
  return $ TermBox t'
elaborate' (_ :< NeutBoxIntro t) = do
  t' <- elaborate' t
  return $ TermBoxIntro t'
elaborate' (_ :< NeutBoxElim t) = do
  t' <- elaborate' t
  return $ TermBoxElim t'
elaborate' (_ :< NeutIndex s) = return $ TermIndex s
elaborate' (meta :< NeutIndexIntro x) = return $ TermIndexIntro x meta
elaborate' (_ :< NeutIndexElim e branchList) = do
  e' <- elaborate' e
  branchList' <-
    forM branchList $ \(l, body) -> do
      body' <- elaborate' body
      return (l, body')
  return $ TermIndexElim e' branchList'
elaborate' (_ :< NeutConst t) = do
  t' <- elaborate' t
  return $ TermConst t'
elaborate' (_ :< NeutConstIntro s) = return $ TermConstIntro s
elaborate' (_ :< NeutConstElim e) = do
  e' <- elaborate' e
  return $ TermConstElim e'
elaborate' (_ :< NeutUniv j) = return $ TermUniv j
elaborate' (_ :< NeutMu s e) = do
  e' <- elaborate' e
  return $ TermMu s e'
elaborate' (_ :< NeutHole x) = do
  sub <- gets substitution
  tenv <- gets typeEnv
  case lookup x $ sub ++ tenv of
    Just e -> elaborate' e
    Nothing -> lift $ throwE $ "elaborate': remaining hole: " ++ x

sigmaSize :: Neut -> Int
sigmaSize (_ :< NeutSigma xts t) = do
  let ts = map snd xts ++ [t]
  maximum $ map sizeOf ts
sigmaSize _ = 64
