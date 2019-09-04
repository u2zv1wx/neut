module Elaborate
  ( elaborate
  ) where

import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.IORef
import           Data.List                  (nub)
import qualified Data.Map.Strict            as Map

import           Data.Basic
import           Data.Env
import           Data.Term
import           Data.WeakTerm
import           Elaborate.Analyze
import           Elaborate.Infer
import           Elaborate.Synthesize
import           Reduce.Term
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
elaborate :: WeakTermPlus -> WithEnv TermPlus
elaborate e = do
  _ <- infer [] e
  -- Kantian type-inference ;)
  gets constraintEnv >>= analyze
  gets constraintQueue >>= synthesize
  -- update the type environment by resulting substitution
  sub <- gets substEnv
  tenv <- gets typeEnv
  let tenv' = Map.map (substWeakTermPlus sub) tenv
  modify (\env -> env {typeEnv = tenv'})
  -- use the resulting substitution to elaborate `e`.
  let e' = substWeakTermPlus sub e
  exhaust e' >>= elaborate'

-- This function translates a well-typed term into an untyped term in a
-- reduction-preserving way. Here, we translate types into units (nullary product).
-- This doesn't cause any problem since types doesn't have any beta-reduction.
elaborate' :: WeakTermPlus -> WithEnv TermPlus
elaborate' (m, WeakTermTau) = do
  m' <- toMeta m
  ensuringTypePurity (m', TermTau)
elaborate' (m, WeakTermTheta x) = do
  m' <- toMeta m
  ensuringTypePurity (m', TermTheta x)
elaborate' (m, WeakTermUpsilon x) = do
  m' <- toMeta m
  ensuringTypePurity (m', TermUpsilon x)
elaborate' (m, WeakTermEpsilon k) = do
  m' <- toMeta m
  ensuringTypePurity (m', TermEpsilon k)
elaborate' (m, WeakTermEpsilonIntro x) = do
  m' <- toMeta m
  t <- reduceTermPlus $ obtainType m'
  case t of
    (_, TermEpsilon _) -> ensuringTypePurity (m', TermEpsilonIntro x undefined)
    _ -> throwError "epsilonIntro"
elaborate' (m, WeakTermEpsilonElim (x, t) e branchList) = do
  t' <- elaborate' t >>= reduceTermPlus
  case t' of
    (_, TermEpsilon _) -> do
      m' <- toMeta m
      e' <- elaborate' e
      branchList' <- forM branchList elaboratePlus
      ensuringTypePurity (m', TermEpsilonElim (x, t') e' branchList')
    _ -> throwError "epsilonElim"
elaborate' (m, WeakTermPi xts) = do
  m' <- toMeta m
  xts' <- mapM elaboratePlus xts
  ensuringTypePurity (m', TermPi xts')
elaborate' (m, WeakTermPiIntro xts e) = do
  m' <- toMeta m
  e' <- elaborate' e
  xts' <- mapM elaboratePlus xts
  ensuringTypePurity (m', TermPiIntro xts' e')
elaborate' (m, WeakTermPiElim e es) = do
  m' <- toMeta m
  e' <- elaborate' e
  es' <- mapM elaborate' es
  ensuringTypePurity (m', TermPiElim e' es')
elaborate' (m, WeakTermMu (x, t) e) = do
  t' <- elaborate' t >>= reduceTermPlus
  case t' of
    (_, TermPi _) -> do
      m' <- toMeta m
      e' <- elaborate' e
      ensuringTypePurity (m', TermMu (x, t') e')
    _ -> lift $ throwE "CBV recursion is allowed only for Pi-types"
elaborate' (_, WeakTermZeta x) = do
  sub <- gets substEnv
  case lookup x sub of
    Just e  -> elaborate' e
    Nothing -> lift $ throwE $ "elaborate' i: remaining hole: " ++ x

elaboratePlus :: (a, WeakTermPlus) -> WithEnv (a, TermPlus)
elaboratePlus (x, t) = do
  t' <- elaborate' t
  return (x, t')

exhaust :: WeakTermPlus -> WithEnv WeakTermPlus
exhaust e = do
  b <- exhaust' e
  if b
    then return e
    else lift $ throwE "non-exhaustive pattern"

exhaust' :: WeakTermPlus -> WithEnv Bool
exhaust' (_, WeakTermTau) = return True
exhaust' (_, WeakTermTheta _) = return True
exhaust' (_, WeakTermUpsilon _) = return True
exhaust' (_, WeakTermEpsilon _) = return True
exhaust' (_, WeakTermEpsilonIntro _) = return True
exhaust' (_, WeakTermEpsilonElim (_, t) e1 branchList) = do
  b1 <- exhaust' e1
  let labelList = map fst branchList
  t' <- reduceWeakTermPlus t
  case t' of
    (_, WeakTermEpsilon x) -> exhaustEpsilonIdentifier x labelList b1
    _                      -> lift $ throwE "type error (exhaust)"
exhaust' (_, WeakTermPi xts) = allM exhaust' $ map snd xts
exhaust' (_, WeakTermPiIntro _ e) = exhaust' e
exhaust' (_, WeakTermPiElim e es) = allM exhaust' $ e : es
exhaust' (_, WeakTermMu _ e) = exhaust' e
exhaust' (_, WeakTermZeta _) = return False

exhaustEpsilonIdentifier :: Identifier -> [Case] -> Bool -> WithEnv Bool
exhaustEpsilonIdentifier x labelList b1 = do
  ienv <- gets epsilonEnv
  case lookup x ienv of
    Nothing -> undefined -- xはi32とかそのへんのやつ
    Just ls ->
      if length ls <= length (nub labelList)
        then return $ b1 && True
        else return False

ensuringTypePurity :: TermPlus -> WithEnv TermPlus
ensuringTypePurity t@(MetaTerminal _, _) =
  if not (isPure t)
    then throwError "impure type"
    else return t
ensuringTypePurity t@(MetaNonTerminal t1 ml, e) =
  if not (isPure t1)
    then throwError "impure type"
    else do
      t1' <- reduceTermPlus t1 -- t1はpureだと分かっているので普通にreduceしてよい
      case t1' of
        (_, TermTau) -> ensuringTypePurity (MetaTerminal ml, e)
        _            -> return t

allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM _ [] = return True
allM p (x:xs) = do
  b1 <- p x
  b2 <- allM p xs
  return $ b1 && b2

toMeta :: WeakMeta -> WithEnv Meta
toMeta (WeakMetaTerminal l) = return $ MetaTerminal l
toMeta (WeakMetaNonTerminal (Ref r) l) = do
  mt <- liftIO $ readIORef r
  case mt of
    Nothing -> undefined
    Just t -> do
      t' <- elaborate' t
      return $ MetaNonTerminal t' l

obtainType :: Meta -> TermPlus
obtainType (MetaTerminal _)      = (MetaTerminal Nothing, TermTau)
obtainType (MetaNonTerminal t _) = t
