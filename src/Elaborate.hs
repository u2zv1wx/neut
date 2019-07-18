module Elaborate
  ( elaborate
  ) where

import           Control.Comonad.Cofree
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
  exhaust e' >>= elaborate' 0

-- This function translates a well-typed term into an untyped term in a
-- reduction-preserving way. Here, we translate types into units (nullary product).
-- This doesn't cause any problem since types doesn't have any beta-reduction.
elaborate' :: Int -> WeakTerm -> WithEnv Term
elaborate' _ (_ :< WeakTermUniv _) = return zero
elaborate' _ (_ :< WeakTermUpsilon x) = return $ TermUpsilon x
elaborate' _ (_ :< WeakTermEpsilon _) = return zero
elaborate' _ (meta :< WeakTermEpsilonIntro x) = do
  t <- lookupTypeEnv' meta
  case reduceWeakTerm t of
    _ :< WeakTermEpsilon i -> return $ TermEpsilonIntro x (asLowType i)
    _                      -> lift $ throwE "epsilon"
elaborate' i (_ :< WeakTermEpsilonElim (x, _) e branchList) = do
  e' <- elaborate' i e
  branchList' <-
    forM branchList $ \(l, body) -> do
      body' <- elaborate' i body
      return (l, body')
  return $ TermEpsilonElim x e' branchList'
elaborate' _ (_ :< WeakTermConst x) = return $ TermConst x
elaborate' _ (_ :< WeakTermPi _) = return zero
elaborate' i (m :< WeakTermPiIntro xts e) = do
  e' <- elaborate' i e
  l <- obtainLevel m
  return $ TermPiIntro l (map fst xts) e'
elaborate' i (_ :< WeakTermPiElim e es) = do
  e' <- elaborate' i e
  es' <- mapM (elaborate' i) es
  return $ TermPiElim e' es'
elaborate' _ (_ :< WeakTermSigma _) = return zero
elaborate' i (m :< WeakTermSigmaIntro es) = do
  es' <- mapM (elaborate' i) es
  l <- obtainLevel m
  return $ TermSigmaIntro l es'
elaborate' i (_ :< WeakTermSigmaElim xts e1 e2) = do
  e1' <- elaborate' i e1
  e2' <- elaborate' i e2
  return $ TermSigmaElim (map fst xts) e1' e2'
elaborate' _ (_ :< WeakTermTau _) = return zero
elaborate' i (_ :< WeakTermTauIntro e) = do
  e' <- elaborate' (i + 1) e
  return $ TermTauIntro e'
elaborate' i (_ :< WeakTermTauElim e) = do
  e' <- elaborate' (i - 1) e
  return $ TermTauElim e'
elaborate' _ (_ :< WeakTermTheta _) = return zero
elaborate' i (_ :< WeakTermThetaIntro e) = do
  l <- withOffset i
  o <- obtainOrigin
  e' <- elaborate' i e
  l' <- withOffset' $ -i
  return $
    TermPiIntro LevelInfinity [o] (TermPiElim (TermPiIntro l [o] e') [l'])
elaborate' i (_ :< WeakTermThetaElim e) = do
  l <- withOffset' i
  e' <- elaborate' i e
  return $ TermPiElim e' [l]
elaborate' i (meta :< WeakTermMu (x, t) e) =
  case reduceWeakTerm t of
    _ :< WeakTermPi _ -> do
      e' <- elaborate' i e
      let fvs = varWeakTerm $ meta :< WeakTermMu (x, t) e
      insTermEnv x fvs $
        substTerm [(x, TermConstElim x (map TermUpsilon fvs))] e'
      return $ TermConstElim x (map TermUpsilon fvs)
    _ -> lift $ throwE "CBV recursion is allowed only for Pi-types"
elaborate' i (_ :< WeakTermIota e _) = elaborate' i e
elaborate' i (_ :< WeakTermHole x) = do
  sub <- gets substEnv
  case lookup x sub of
    Just e  -> elaborate' i e
    Nothing -> lift $ throwE $ "elaborate' i: remaining hole: " ++ x

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
exhaust' (_ :< WeakTermEpsilonElim (_, t) e1 branchList) = do
  b1 <- exhaust' e1
  let labelList = map fst branchList
  case reduceWeakTerm t of
    _ :< WeakTermEpsilon x -> exhaustEpsilonIdentifier x labelList b1
    _                      -> lift $ throwE "type error (exhaust)"
exhaust' (_ :< WeakTermPi xts) = allM exhaust' $ map snd xts
exhaust' (_ :< WeakTermPiIntro _ e) = exhaust' e
exhaust' (_ :< WeakTermPiElim e es) = allM exhaust' $ e : es
exhaust' (_ :< WeakTermSigma xts) = allM exhaust' $ map snd xts
exhaust' (_ :< WeakTermSigmaIntro es) = allM exhaust' es
exhaust' (_ :< WeakTermSigmaElim _ e1 e2) = allM exhaust' [e1, e2]
exhaust' (_ :< WeakTermTau t) = exhaust' t
exhaust' (_ :< WeakTermTauIntro e) = exhaust' e
exhaust' (_ :< WeakTermTauElim e) = exhaust' e
exhaust' (_ :< WeakTermTheta t) = exhaust' t
exhaust' (_ :< WeakTermThetaIntro e) = exhaust' e
exhaust' (_ :< WeakTermThetaElim e) = exhaust' e
exhaust' (_ :< WeakTermMu _ e) = exhaust' e
exhaust' (_ :< WeakTermIota e _) = exhaust' e
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

obtainLevel :: Identifier -> WithEnv Level
obtainLevel m = do
  typeMeta :< _ <- lookupTypeEnv' m
  u <- lookupTypeEnv' typeMeta
  case reduceWeakTerm u of
    _ :< WeakTermUniv wl ->
      case wl of
        WeakLevelInt i    -> withOffset i
        WeakLevelInfinity -> return LevelInfinity
        WeakLevelHole _   -> undefined
    _ -> lift $ throwE "obtainLevel"

withOffset :: Int -> WithEnv Level
withOffset i = LevelInt <$> withOffset' i
  -- o <- obtainOrigin
  -- let l = TermEpsilonIntro (LiteralInteger i) (LowTypeSignedInt 64)
  -- return $ LevelInt $ TermConstElim "core.i64.add" [TermUpsilon o, l]

withOffset' :: Int -> WithEnv Term
withOffset' i = do
  o <- obtainOrigin
  let l = TermEpsilonIntro (LiteralInteger i) (LowTypeSignedInt 64)
  return $ TermConstElim "core.i64.add" [TermUpsilon o, l]

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
