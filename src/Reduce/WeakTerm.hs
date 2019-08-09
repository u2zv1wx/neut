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
reduceWeakTerm (m :< WeakTermPiElim e es) = do
  es' <- mapM reduceWeakTerm es
  e' <- reduceWeakTerm e
  case e' of
    _ :< WeakTermPiIntro xts body
      | length xts == length es'
      , all isValue es' -> do
        let xs = map fst xts
        reduceWeakTerm $ substWeakTerm (zip xs es') body
    self@(_ :< WeakTermMu (x, _) body) -> do
      let self' = substWeakTerm [(x, self)] body
      reduceWeakTerm (m :< WeakTermPiElim self' es')
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
          _ -> return $ m :< WeakTermPiElim e' es'
    _ -> return $ m :< WeakTermPiElim e' es'
reduceWeakTerm (m :< WeakTermSigmaIntro es) = do
  es' <- mapM reduceWeakTerm es
  return $ m :< WeakTermSigmaIntro es'
reduceWeakTerm (m :< WeakTermSigmaElim xts e1 e2) = do
  e1' <- reduceWeakTerm e1
  case e1' of
    _ :< WeakTermSigmaIntro es
      | length es == length xts -> do
        let xs = map fst xts
        reduceWeakTerm $ substWeakTerm (zip xs es) e2
    _ -> return $ m :< WeakTermSigmaElim xts e1' e2
reduceWeakTerm t = return t
