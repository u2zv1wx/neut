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
  nonRecReduce (subst sub e) >>= exhaust >>= insWeakTermEnv main

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

elaborate' :: Neut -> WithEnv Neut
elaborate' = undefined
