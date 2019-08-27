module Reduce.WeakTerm
  ( reduceWeakTermPlus
  ) where

import           Data.Basic
import           Data.Env
import           Data.WeakTerm

reduceWeakTermPlus :: WeakTermPlus -> WithEnv WeakTermPlus
reduceWeakTermPlus (m, WeakTermEpsilonElim (x, t) e branchList) = do
  e' <- reduceWeakTermPlus e
  case e' of
    (_, WeakTermEpsilonIntro l) ->
      case lookup (CaseLiteral l) branchList of
        Just body -> reduceWeakTermPlus $ substWeakTermPlus [(x, e')] body
        Nothing ->
          case lookup CaseDefault branchList of
            Just body -> reduceWeakTermPlus $ substWeakTermPlus [(x, e')] body
            Nothing -> return (m, WeakTermEpsilonElim (x, t) e' branchList)
    _ -> return (m, WeakTermEpsilonElim (x, t) e' branchList)
reduceWeakTermPlus (m, WeakTermPiElim e es) = do
  e' <- reduceWeakTermPlus e
  es' <- mapM reduceWeakTermPlus es
  case e' of
    (_, WeakTermPiIntro xts body)
      | length xts == length es'
      , all isValue es' -> do
        let xs = map fst xts
        reduceWeakTermPlus $ substWeakTermPlus (zip xs es') body
    self@(_, WeakTermMu (x, _) body)
      | all isValue es' -> do
        let self' = substWeakTermPlus [(x, self)] body
        reduceWeakTermPlus (m, WeakTermPiElim self' es')
    (_, WeakTermTheta constant)
      | [(_, WeakTermEpsilonIntro (LiteralInteger x)), (_, WeakTermEpsilonIntro (LiteralInteger y))] <-
         es' -> do
        let b1 = constant `elem` intAddConstantList
        let b2 = constant `elem` intSubConstantList
        let b3 = constant `elem` intMulConstantList
        let b4 = constant `elem` intDivConstantList
        case (b1, b2, b3, b4) of
          (True, _, _, _) ->
            return (m, WeakTermEpsilonIntro (LiteralInteger (x + y)))
          (_, True, _, _) ->
            return (m, WeakTermEpsilonIntro (LiteralInteger (x - y)))
          (_, _, True, _) ->
            return (m, WeakTermEpsilonIntro (LiteralInteger (x * y)))
          (_, _, _, True) ->
            return (m, WeakTermEpsilonIntro (LiteralInteger (x `div` y)))
          _ -> return (m, WeakTermPiElim e' es')
    _ -> return (m, WeakTermPiElim e' es')
reduceWeakTermPlus t = return t
