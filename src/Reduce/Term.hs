module Reduce.Term
  ( reduceTerm
  ) where

import           Control.Comonad.Cofree

import           Data.Basic
import           Data.Env
import           Data.Term

reduceTerm :: Term -> WithEnv Term
reduceTerm (m :< TermEpsilonElim (x, t) e branchList) = do
  e' <- reduceTerm e
  case e' of
    _ :< TermEpsilonIntro l ->
      case lookup (CaseLiteral l) branchList of
        Just body -> reduceTerm $ substTerm [(x, e')] body
        Nothing ->
          case lookup CaseDefault branchList of
            Just body -> reduceTerm $ substTerm [(x, e')] body
            Nothing   -> return $ m :< TermEpsilonElim (x, t) e' branchList
    _ -> return $ m :< TermEpsilonElim (x, t) e' branchList
reduceTerm (m :< TermPiElim e es) = do
  e' <- reduceTerm e
  es' <- mapM reduceTerm es
  case e' of
    _ :< TermPiIntro xts body
      | length xts == length es'
      , all isValue es' -> do
        let xs = map fst xts
        reduceTerm $ substTerm (zip xs es') body
    self@(_ :< TermMu (x, _) body)
      | all isValue es' -> do
        let self' = substTerm [(x, self)] body
        reduceTerm (m :< TermPiElim self' es')
    _ :< TermTheta constant
      | [_ :< TermEpsilonIntro (LiteralInteger x), _ :< TermEpsilonIntro (LiteralInteger y)] <-
         es' -> do
        let b1 = constant `elem` intAddConstantList
        let b2 = constant `elem` intSubConstantList
        let b3 = constant `elem` intMulConstantList
        let b4 = constant `elem` intDivConstantList
        case (b1, b2, b3, b4) of
          (True, _, _, _) ->
            return $ m :< TermEpsilonIntro (LiteralInteger (x + y))
          (_, True, _, _) ->
            return $ m :< TermEpsilonIntro (LiteralInteger (x - y))
          (_, _, True, _) ->
            return $ m :< TermEpsilonIntro (LiteralInteger (x * y))
          (_, _, _, True) ->
            return $ m :< TermEpsilonIntro (LiteralInteger (x `div` y))
          _ -> return $ m :< TermPiElim e' es'
    _ -> return $ m :< TermPiElim e' es'
reduceTerm (m :< TermSigmaIntro es) = do
  es' <- mapM reduceTerm es
  return $ m :< TermSigmaIntro es'
reduceTerm (m :< TermSigmaElim xts e1 e2) = do
  e1' <- reduceTerm e1
  case e1' of
    _ :< TermSigmaIntro es
      | length es == length xts
      , all isValue es -> do
        let xs = map fst xts
        reduceTerm $ substTerm (zip xs es) e2
    _ -> return $ m :< TermSigmaElim xts e1' e2
reduceTerm t = return t
