module Elaborate
  ( elaborate
  ) where

import           Control.Comonad.Cofree
import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.List                  (nub)
import qualified Data.Map.Strict            as Map
import           Text.Read                  (readMaybe)

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
  sub <- gets substEnv
  tenv <- gets typeEnv
  let tenv' = Map.map (substWeakTerm sub) tenv
  modify (\env -> env {typeEnv = tenv'})
  -- use the resulting substitution to elaborate `e`.
  let e' = substWeakTerm sub e
  exhaust e' >>= elaborate'

-- This function translates a well-typed term into an untyped term in a
-- reduction-preserving way. Here, we translate types into units (nullary product).
-- This doesn't cause any problem since types doesn't have any beta-reduction.
elaborate' :: WeakTerm -> WithEnv Term
elaborate' (_ :< WeakTermUniverse) = return zero
elaborate' (_ :< WeakTermUpsilon x) = return $ TermUpsilon x
elaborate' (_ :< WeakTermEpsilon _) = return one -- immediate type
elaborate' (meta :< WeakTermEpsilonIntro x) = do
  t <- lookupTypeEnv' meta
  t' <- reduceWeakTerm t
  case t' of
    _ :< WeakTermEpsilon i -> return $ TermEpsilonIntro x (asLowType i)
    _                      -> lift $ throwE "epsilon"
elaborate' (_ :< WeakTermEpsilonElim (x, _) e branchList) = do
  e' <- elaborate' e
  branchList' <-
    forM branchList $ \(l, body) -> do
      body' <- elaborate' body
      return (l, body')
  return $ TermEpsilonElim x e' branchList'
elaborate' (_ :< WeakTermConst x) = return $ TermConst x
elaborate' (_ :< WeakTermPi _) = return zero
elaborate' (_ :< WeakTermPiIntro xts e) = do
  e' <- elaborate' e
  return $ TermPiIntro (map fst xts) e'
elaborate' (_ :< WeakTermPiElim e es) = do
  e' <- elaborate' e
  es' <- mapM elaborate' es
  return $ TermPiElim e' es'
elaborate' (_ :< WeakTermSigma _) = return zero
elaborate' (_ :< WeakTermSigmaIntro es) = do
  es' <- mapM elaborate' es
  return $ TermSigmaIntro es'
elaborate' (_ :< WeakTermSigmaElim xts e1 e2) = do
  e1' <- elaborate' e1
  e2' <- elaborate' e2
  return $ TermSigmaElim (map fst xts) e1' e2'
elaborate' (meta :< WeakTermMu (x, t) e) = do
  t' <- reduceWeakTerm t
  let fvs = varWeakTerm $ meta :< WeakTermMu (x, t) e
  e' <- elaborate' e
  let fvs' = map TermUpsilon fvs
  insTermEnv x fvs $ substTerm [(x, TermConstElim x fvs')] e'
  case t' of
    _ :< WeakTermPi _ -> return $ TermConstElim x fvs'
    _ ->
      lift $ throwE "CBV recursion is allowed only for Pi-types and Theta-types"
elaborate' (_ :< WeakTermHole x) = do
  sub <- gets substEnv
  case lookup x sub of
    Just e  -> elaborate' e
    Nothing -> lift $ throwE $ "elaborate' i: remaining hole: " ++ x

exhaust :: WeakTerm -> WithEnv WeakTerm
exhaust e = do
  b <- exhaust' e
  if b
    then return e
    else lift $ throwE "non-exhaustive pattern"

exhaust' :: WeakTerm -> WithEnv Bool
exhaust' (_ :< WeakTermUniverse) = return True
exhaust' (_ :< WeakTermUpsilon _) = return True
exhaust' (_ :< WeakTermEpsilon _) = return True
exhaust' (_ :< WeakTermEpsilonIntro _) = return True
exhaust' (_ :< WeakTermEpsilonElim (_, t) e1 branchList) = do
  b1 <- exhaust' e1
  let labelList = map fst branchList
  t' <- reduceWeakTerm t
  case t' of
    _ :< WeakTermEpsilon x -> exhaustEpsilonIdentifier x labelList b1
    _                      -> lift $ throwE "type error (exhaust)"
exhaust' (_ :< WeakTermPi xts) = allM exhaust' $ map snd xts
exhaust' (_ :< WeakTermPiIntro _ e) = exhaust' e
exhaust' (_ :< WeakTermPiElim e es) = allM exhaust' $ e : es
exhaust' (_ :< WeakTermSigma xts) = allM exhaust' $ map snd xts
exhaust' (_ :< WeakTermSigmaIntro es) = allM exhaust' es
exhaust' (_ :< WeakTermSigmaElim _ e1 e2) = allM exhaust' [e1, e2]
exhaust' (_ :< WeakTermMu _ e) = exhaust' e
exhaust' (_ :< WeakTermConst _) = return True
exhaust' (_ :< WeakTermHole _) = return False

exhaustEpsilonIdentifier :: Identifier -> [Case] -> Bool -> WithEnv Bool
exhaustEpsilonIdentifier x labelList b1 = do
  ienv <- gets indexEnv
  case lookup x ienv of
    Nothing -> undefined -- xはi32とかそのへんのやつ
    Just ls ->
      if length ls <= length (nub labelList)
        then return $ b1 && True
        else return False

allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM _ [] = return True
allM p (x:xs) = do
  b1 <- p x
  b2 <- allM p xs
  return $ b1 && b2

zero :: Term
zero = TermEpsilonIntro (LiteralInteger 0) $ LowTypeSignedInt 64

one :: Term
one = TermEpsilonIntro (LiteralInteger 1) $ LowTypeSignedInt 64

asLowType :: Identifier -> LowType
asLowType x
  | length x > 1
  , 'i' <- head x
  , Just i <- readMaybe (tail x)
  , 1 <= i
  , i <= 2 ^ (23 :: Int) - 1 = LowTypeSignedInt i
asLowType x
  | length x > 1
  , 'u' <- head x
  , Just i <- readMaybe (tail x)
  , 1 <= i
  , i <= 2 ^ (23 :: Int) - 1 = LowTypeUnsignedInt i
asLowType x
  | length x > 1
  , 'f' <- head x
  , Just i <- readMaybe (tail x)
  , i `elem` [16, 32, 64] = LowTypeFloat i
asLowType _ = LowTypeSignedInt 64 -- sortals are represented as int
