module Elaborate
  ( elaborate
  ) where

import           Control.Comonad.Cofree
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.List                  (nub)
import qualified Data.Map.Strict            as Map
import qualified Text.Show.Pretty           as Pr

import           Data.Basic
import           Data.Env
import           Data.Term
import           Data.WeakTerm
import           Elaborate.Analyze
import           Elaborate.Infer
import           Elaborate.Synthesize
import           Reduce.WeakTerm

-- Given a term `e` and its name `main`, this function
--   (1) traces `e` using `infer e`, collecting type constraints,
--   (2) updates typeEnv for `main` by the result of `infer e`,
--   (3) analyze the constraints, solving easy ones,
--   (4) synthesize these analyzed constraints, solving as many solutions as possible,
--   (5) elaborate the given term using the result of synthesis.
-- The inference algorithm in this module is based on L. de Moura, J. Avigad,
-- S. Kong, and C. Roux. "Elaboration in Dependent Type Theory", arxiv,
-- https://arxiv.org/abs/1505.04324, 2015.
elaborate :: WeakTerm -> WithEnv Term
elaborate e = do
  _ <- infer [] e
  -- Kantian type-inference ;)
  gets constraintEnv >>= analyze
  gets constraintQueue >>= synthesize
  -- update the type environment by resulting substitution
  sub <- gets substitution
  tenv <- gets typeEnv
  let tenv' = Map.map (substWeakTerm sub) tenv
  modify (\env -> env {typeEnv = tenv'})
  -- use the resulting substitution to elaborate `e`.
  exhaust e >>= elaborate'

getNumLowType :: Identifier -> WithEnv (Either WeakTerm LowType)
getNumLowType meta = do
  t <- lookupTypeEnv' meta >>= reduceWeakTerm
  case t of
    _ :< WeakTermIndex "i1"  -> return $ Right $ LowTypeSignedInt 1
    _ :< WeakTermIndex "i2"  -> return $ Right $ LowTypeSignedInt 2
    _ :< WeakTermIndex "i4"  -> return $ Right $ LowTypeSignedInt 4
    _ :< WeakTermIndex "i8"  -> return $ Right $ LowTypeSignedInt 8
    _ :< WeakTermIndex "i16" -> return $ Right $ LowTypeSignedInt 16
    _ :< WeakTermIndex "i32" -> return $ Right $ LowTypeSignedInt 32
    _ :< WeakTermIndex "i64" -> return $ Right $ LowTypeSignedInt 64
    _ :< WeakTermIndex "u1"  -> return $ Right $ LowTypeUnsignedInt 1
    _ :< WeakTermIndex "u2"  -> return $ Right $ LowTypeUnsignedInt 2
    _ :< WeakTermIndex "u4"  -> return $ Right $ LowTypeUnsignedInt 4
    _ :< WeakTermIndex "u8"  -> return $ Right $ LowTypeUnsignedInt 8
    _ :< WeakTermIndex "u16" -> return $ Right $ LowTypeUnsignedInt 16
    _ :< WeakTermIndex "u32" -> return $ Right $ LowTypeUnsignedInt 32
    _ :< WeakTermIndex "u64" -> return $ Right $ LowTypeUnsignedInt 64
    _ :< WeakTermIndex "f16" -> return $ Right $ LowTypeFloat 16
    _ :< WeakTermIndex "f32" -> return $ Right $ LowTypeFloat 32
    _ :< WeakTermIndex "f64" -> return $ Right $ LowTypeFloat 64
    _ :< WeakTermIndex _     -> return $ Right $ LowTypeSignedInt 64 -- label is int
    _                        -> return $ Left t

-- This function translates a well-typed term into an untyped term in a
-- reduction-preserving way. Here, we translate types into units (nullary product).
-- This doesn't cause any problem since types doesn't have any beta-reduction.
elaborate' :: WeakTerm -> WithEnv Term
elaborate' (_ :< WeakTermVar s) = return $ TermVar s
elaborate' (_ :< WeakTermConst x) = return $ TermConst x
elaborate' (_ :< WeakTermPi _ _) = return $ TermSigmaIntro []
elaborate' (_ :< WeakTermPiIntro (x, _) e) = do
  e' <- elaborate' e
  return $ TermPiIntro x e'
elaborate' (_ :< WeakTermPiElim e v) = do
  e' <- elaborate' e
  v' <- elaborate' v
  return $ TermPiElim e' v'
elaborate' (_ :< WeakTermSigma _) = return $ TermSigmaIntro []
elaborate' (_ :< WeakTermSigmaIntro es) = do
  es' <- mapM elaborate' es
  return $ TermSigmaIntro es'
elaborate' (_ :< WeakTermSigmaElim xs e1 e2) = do
  e1' <- elaborate' e1
  e2' <- elaborate' e2
  return $ TermSigmaElim xs e1' e2'
elaborate' (_ :< WeakTermIndex _) = return $ TermSigmaIntro []
elaborate' (meta :< WeakTermIndexIntro x) = do
  mt <- getNumLowType meta
  case mt of
    Right t -> return $ TermIndexIntro x t
    Left t ->
      lift $
      throwE $
      "the type of " ++
      show x ++ " is supposed to be a number, but is " ++ Pr.ppShow t
elaborate' (_ :< WeakTermIndexElim e branchList) = do
  e' <- elaborate' e
  branchList' <-
    forM branchList $ \(l, body) -> do
      body' <- elaborate' body
      return (l, body')
  return $ TermIndexElim e' branchList'
elaborate' (_ :< WeakTermUniv _) = return $ TermSigmaIntro []
elaborate' (meta :< WeakTermFix x e) = do
  e' <- elaborate' e
  let fvs = varWeakTerm $ meta :< WeakTermFix x e
  insTermEnv x fvs $ substTerm [(x, TermConstElim x (map TermVar fvs))] e'
  return $ TermConstElim x (map TermVar fvs)
elaborate' (_ :< WeakTermHole x) = do
  sub <- gets substitution
  case lookup x sub of
    Just e  -> elaborate' e
    Nothing -> lift $ throwE $ "elaborate': remaining hole: " ++ x

exhaust :: WeakTerm -> WithEnv WeakTerm
exhaust e = do
  b <- exhaust' e
  if b
    then return e
    else lift $ throwE "non-exhaustive pattern"

exhaust' :: WeakTerm -> WithEnv Bool
exhaust' (_ :< WeakTermVar _) = return True
exhaust' (_ :< WeakTermConst _) = return True
exhaust' (_ :< WeakTermPi (_, tdom) tcod) = allM exhaust' [tdom, tcod]
exhaust' (_ :< WeakTermPiIntro _ e) = exhaust' e
exhaust' (_ :< WeakTermPiElim e1 e2) = allM exhaust' [e1, e2]
exhaust' (_ :< WeakTermSigma xts) = allM exhaust' $ map snd xts
exhaust' (_ :< WeakTermSigmaIntro es) = allM exhaust' es
exhaust' (_ :< WeakTermSigmaElim _ e1 e2) = allM exhaust' [e1, e2]
exhaust' (_ :< WeakTermFix _ e) = exhaust' e
exhaust' (_ :< WeakTermIndex _) = return True
exhaust' (_ :< WeakTermIndexIntro _) = return True
exhaust' (_ :< WeakTermIndexElim _ []) = return False -- empty clause?
exhaust' (meta :< WeakTermIndexElim e1 branchList@((l, _):_)) = do
  b1 <- exhaust' e1
  t <- lookupTypeEnv' meta >>= reduceWeakTerm
  let labelList = map fst branchList
  case t of
    _ :< WeakTermIndex "i32" -> return $ b1 && (IndexDefault `elem` labelList)
    _
      | IndexDefault `elem` labelList -> return b1
    _ ->
      case l of
        IndexLabel x -> do
          set <- lookupIndexSet x
          if length set <= length (nub labelList)
            then return True
            else return False
        _ -> return False
exhaust' (_ :< WeakTermUniv _) = return True
exhaust' (_ :< WeakTermHole _) = return False

allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM _ [] = return True
allM p (x:xs) = do
  b1 <- p x
  b2 <- allM p xs
  return $ b1 && b2
