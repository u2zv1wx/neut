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

import qualified Data.Map.Strict as Map

import Data.Maybe

import qualified Data.PQueue.Min as Q

-- Given a term `e` and its name `main`, this function
--   (1) traces `e` using `infer e`, collecting type constraints,
--   (2) updates typeEnv for `main` by the result of `infer e`,
--   (3) analyze the constraints, solving easy ones,
--   (4) synthesize these analyzed constraints, solving as many solutions as possible,
--   (5) elaborate the given term using the result of synthesis.
-- The inference algorithm in this module is based on L. de Moura, J. Avigad,
-- S. Kong, and C. Roux. "Elaboration in Dependent Type Theory", arxiv,
-- https://arxiv.org/abs/1505.04324, 2015.
elaborate :: Neut -> WithEnv Term
elaborate e = do
  _ <- infer [] e
  -- Kantian type-inference ;)
  gets constraintEnv >>= analyze
  gets constraintQueue >>= synthesize
  -- update the type environment by resulting substitution
  sub <- gets substitution
  tenv <- gets typeEnv
  let tenv' = Map.map (subst sub) tenv
  modify (\e -> e {typeEnv = tenv'})
  -- use the resulting substitution to elaborate `e`.
  exhaust e >>= elaborate'

getNumLowType :: Identifier -> WithEnv (Either Neut LowType)
getNumLowType meta = do
  t <- lookupTypeEnv' meta >>= reduce
  case t of
    _ :< NeutIndex "i1" -> return $ Right $ LowTypeSignedInt 1
    _ :< NeutIndex "i2" -> return $ Right $ LowTypeSignedInt 2
    _ :< NeutIndex "i4" -> return $ Right $ LowTypeSignedInt 4
    _ :< NeutIndex "i8" -> return $ Right $ LowTypeSignedInt 8
    _ :< NeutIndex "i16" -> return $ Right $ LowTypeSignedInt 16
    _ :< NeutIndex "i32" -> return $ Right $ LowTypeSignedInt 32
    _ :< NeutIndex "i64" -> return $ Right $ LowTypeSignedInt 64
    _ :< NeutIndex "u1" -> return $ Right $ LowTypeUnsignedInt 1
    _ :< NeutIndex "u2" -> return $ Right $ LowTypeUnsignedInt 2
    _ :< NeutIndex "u4" -> return $ Right $ LowTypeUnsignedInt 4
    _ :< NeutIndex "u8" -> return $ Right $ LowTypeUnsignedInt 8
    _ :< NeutIndex "u16" -> return $ Right $ LowTypeUnsignedInt 16
    _ :< NeutIndex "u32" -> return $ Right $ LowTypeUnsignedInt 32
    _ :< NeutIndex "u64" -> return $ Right $ LowTypeUnsignedInt 64
    _ :< NeutIndex "f16" -> return $ Right $ LowTypeFloat 16
    _ :< NeutIndex "f32" -> return $ Right $ LowTypeFloat 32
    _ :< NeutIndex "f64" -> return $ Right $ LowTypeFloat 64
    t -> return $ Left t

-- This function translates a well-typed term into an untyped term in a
-- reduction-preserving way. Here, we translate types into units (nullary product).
-- This doesn't cause any problem since types doesn't have any beta-reduction.
elaborate' :: Neut -> WithEnv Term
elaborate' (_ :< NeutVar s) = return $ TermVar s
elaborate' (_ :< NeutConst x) = return $ TermConst x
elaborate' (_ :< NeutPi _ _) = return $ TermSigmaIntro []
elaborate' (_ :< NeutPiIntro (x, _) e) = do
  e' <- elaborate' e
  return $ TermPiIntro x e'
elaborate' (_ :< NeutPiElim e v) = do
  e' <- elaborate' e
  v' <- elaborate' v
  return $ TermPiElim e' v'
elaborate' (_ :< NeutSigma _) = return $ TermSigmaIntro []
elaborate' (_ :< NeutSigmaIntro es) = do
  es' <- mapM elaborate' es
  return $ TermSigmaIntro es'
elaborate' (_ :< NeutSigmaElim e1 xs e2) = do
  e1' <- elaborate' e1
  e2' <- elaborate' e2
  return $ TermSigmaElim e1' xs e2'
elaborate' (_ :< NeutIndex _) = return $ TermSigmaIntro []
elaborate' (meta :< NeutIndexIntro x) = do
  mt <- getNumLowType meta
  case mt of
    Right t -> return $ TermIndexIntro x t
    Left t ->
      lift $
      throwE $
      "the type of " ++
      show x ++ " is supposed to be a number, but is " ++ Pr.ppShow t
elaborate' (_ :< NeutIndexElim e branchList) = do
  e' <- elaborate' e
  branchList' <-
    forM branchList $ \(l, body) -> do
      body' <- elaborate' body
      return (l, body')
  return $ TermIndexElim e' branchList'
elaborate' (_ :< NeutUniv _) = return $ TermSigmaIntro []
elaborate' (meta :< NeutMu x e) = do
  e' <- elaborate' e
  let fvs = var $ meta :< NeutMu x e
  env <- newNameWith "env"
  -- Let us define (x1, ..., xn) := (all the free variables in e).
  -- We translate `mu x. e` into
  --   (mu x. lam env. let (x1, ..., xn) := env in e {x := x @ env}) @ (x1, ..., xn)
  -- so that `TermMu x e` doesn't have any free variables.
  return $
    TermPiElim
      (TermMu x $
       TermPiIntro
         env
         (TermSigmaElim
            (TermVar env)
            fvs
            (substTerm [(x, TermPiElim (TermConst x) (TermVar env))] e')))
      (TermSigmaIntro $ map TermVar fvs)
elaborate' (_ :< NeutHole x) = do
  sub <- gets substitution
  case lookup x sub of
    Just e -> elaborate' e
    Nothing -> lift $ throwE $ "elaborate': remaining hole: " ++ x
