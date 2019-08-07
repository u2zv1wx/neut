module Reduce.WeakTerm
  ( reduceWeakTerm
  ) where

import           Control.Comonad.Cofree

import           Data.Basic
import           Data.Env
import           Data.WeakTerm

reduceWeakTerm :: WeakTerm -> WithEnv WeakTerm
reduceWeakTerm (m :< WeakTermEpsilonElim (x, t) e branchList) = do
  e' <- reduceWeakTerm e
  case e' of
    _ :< WeakTermEpsilonIntro l ->
      case lookup (CaseLiteral l) branchList of
        Just body -> reduceWeakTerm $ substWeakTerm [(x, e')] body
        Nothing ->
          case lookup CaseDefault branchList of
            Just body -> reduceWeakTerm $ substWeakTerm [(x, e')] body
            Nothing -> return $ m :< WeakTermEpsilonElim (x, t) e' branchList
    _ -> return $ m :< WeakTermEpsilonElim (x, t) e' branchList
reduceWeakTerm (m :< WeakTermPiElim i e es) = do
  es' <- mapM reduceWeakTerm es
  e' <- reduceWeakTerm e
  case e' of
    _ :< WeakTermPiIntro j xts body
      | length xts == length es'
      , all isValue es' -> do
        insLevelConstraintEnv i j
        let xs = map fst xts
        reduceWeakTerm $ substWeakTerm (zip xs es') body
    self@(_ :< WeakTermMu (x, _) body) -> do
      let self' = substWeakTerm [(x, self)] body
      reduceWeakTerm (m :< WeakTermPiElim i self' es')
    _ :< WeakTermConst constant
      | [_ :< WeakTermEpsilonIntro (LiteralInteger x), _ :< WeakTermEpsilonIntro (LiteralInteger y)] <-
         es' -> do
        let b1 = constant `elem` intAddConstantList
        let b2 = constant `elem` intSubConstantList
        let b3 = constant `elem` intMulConstantList
        let b4 = constant `elem` intDivConstantList
        case (b1, b2, b3, b4) of
          (True, _, _, _) ->
            return $ m :< WeakTermEpsilonIntro (LiteralInteger (x + y))
          (_, True, _, _) ->
            return $ m :< WeakTermEpsilonIntro (LiteralInteger (x - y))
          (_, _, True, _) ->
            return $ m :< WeakTermEpsilonIntro (LiteralInteger (x * y))
          (_, _, _, True) ->
            return $ m :< WeakTermEpsilonIntro (LiteralInteger (x `div` y))
          _ -> return $ m :< WeakTermPiElim i e' es'
    _ -> return $ m :< WeakTermPiElim i e' es'
reduceWeakTerm (m :< WeakTermSigmaIntro i es) = do
  es' <- mapM reduceWeakTerm es
  return $ m :< WeakTermSigmaIntro i es'
reduceWeakTerm (m :< WeakTermSigmaElim i xts e1 e2) = do
  e1' <- reduceWeakTerm e1
  case e1' of
    _ :< WeakTermSigmaIntro j es
      | length es == length xts -> do
        insLevelConstraintEnv i j
        let xs = map fst xts
        reduceWeakTerm $ substWeakTerm (zip xs es) e2
    _ -> return $ m :< WeakTermSigmaElim i xts e1' e2
reduceWeakTerm (m :< WeakTermTauElim i e) = do
  e' <- reduceWeakTerm e
  case e' of
    _ :< WeakTermTauIntro j e'' -> do
      insLevelConstraintEnv i j
      reduceWeakTerm e''
    _ -> return $ m :< WeakTermTauElim i e'
reduceWeakTerm (m :< WeakTermThetaElim e i) = do
  e' <- reduceWeakTerm e
  case e' of
    _ :< WeakTermThetaIntro e'' -> reduceWeakTerm $ shiftWeakTerm i e''
    _                           -> return $ m :< WeakTermThetaElim e' i
reduceWeakTerm t = return t
