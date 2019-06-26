module Elaborate
  ( elaborate
  ) where

import           Control.Comonad.Cofree
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.List                  (nub)
import qualified Data.Map.Strict            as Map
import           Text.Read                  (readMaybe)
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
elaborate' (_ :< WeakTermUniv _) = return zero
elaborate' (_ :< WeakTermUpsilon x) = return $ TermUpsilon x
elaborate' (_ :< WeakTermEpsilon _) = return zero
elaborate' (meta :< WeakTermEpsilonIntro x) = do
  t <- lookupTypeEnv' meta
  mi <- obtainEpsilon t
  case mi of
    Just i  -> return $ TermEpsilonIntro x (asLowType i)
    Nothing -> lift $ throwE "epsilon"
elaborate' (_ :< WeakTermEpsilonElim (_, x) e branchList) = do
  e' <- elaborate' e
  branchList' <-
    forM branchList $ \(l, body) -> do
      body' <- elaborate' body
      return (l, body')
  return $ TermEpsilonElim x e' branchList'
elaborate' (_ :< WeakTermConst x) = return $ TermConst x
elaborate' (_ :< WeakTermPi _ _) = return zero
elaborate' (_ :< WeakTermPiIntro s txs e) = do
  s' <- interpretSortal s
  e' <- elaborate' e
  return $ TermPiIntro s' (map snd txs) e'
elaborate' (_ :< WeakTermPiElim s e es) = do
  s' <- interpretSortal s
  e' <- elaborate' e
  es' <- mapM elaborate' es
  return $ TermPiElim s' e' es'
elaborate' (_ :< WeakTermSigma _ _) = return zero
elaborate' (_ :< WeakTermSigmaIntro s es) = do
  s' <- interpretSortal s
  es' <- mapM elaborate' es
  return $ TermSigmaIntro s' es'
elaborate' (_ :< WeakTermSigmaElim s txs e1 e2) = do
  s' <- interpretSortal s
  e1' <- elaborate' e1
  e2' <- elaborate' e2
  return $ TermSigmaElim s' (map snd txs) e1' e2'
elaborate' (meta :< WeakTermRec (t, x) e) =
  case reduceWeakTerm t of
    _ :< WeakTermPi _ _ -> do
      e' <- elaborate' e
      let fvs = varWeakTerm $ meta :< WeakTermRec (t, x) e
      insTermEnv x fvs $
        substTerm [(x, TermConstElim x (map TermUpsilon fvs))] e'
      return $ TermConstElim x (map TermUpsilon fvs)
    _ -> lift $ throwE "CBV recursion is allowed only for Pi-types"
elaborate' (_ :< WeakTermHole x) = do
  sub <- gets substEnv
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
exhaust' (_ :< WeakTermUniv _) = return True
exhaust' (_ :< WeakTermUpsilon _) = return True
exhaust' (_ :< WeakTermEpsilon _) = return True
exhaust' (_ :< WeakTermEpsilonIntro _) = return True
exhaust' (_ :< WeakTermEpsilonElim (t, _) e1 branchList) = do
  b1 <- exhaust' e1
  let labelList = map fst branchList
  case reduceWeakTerm t of
    _ :< WeakTermEpsilon x -> exhaustEpsilonIdentifier x labelList b1
    _                      -> lift $ throwE "type error (exhaust)"
exhaust' (_ :< WeakTermPi s txs) = allM exhaust' $ s : map fst txs
exhaust' (_ :< WeakTermPiIntro s _ e) = allM exhaust' [s, e]
exhaust' (_ :< WeakTermPiElim s e es) = allM exhaust' $ s : e : es
exhaust' (_ :< WeakTermSigma s txs) = allM exhaust' $ s : map fst txs
exhaust' (_ :< WeakTermSigmaIntro s es) = allM exhaust' $ s : es
exhaust' (_ :< WeakTermSigmaElim s _ e1 e2) = allM exhaust' [s, e1, e2]
exhaust' (_ :< WeakTermRec _ e) = exhaust' e
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

obtainEpsilon :: WeakSortal -> WithEnv (Maybe Identifier)
obtainEpsilon = undefined

interpretSortal :: WeakSortal -> WithEnv Identifier
interpretSortal s =
  case reduceWeakTerm s of
    _ :< WeakTermEpsilonIntro l ->
      case l of
        LiteralLabel x -> return x
        _              -> undefined
    _ -> undefined

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
