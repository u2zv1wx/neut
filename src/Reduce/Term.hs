module Reduce.Term
  ( reduceTermPlus
  ) where

import Data.Basic
import Data.Env
import Data.Term

reduceTermPlus :: TermPlus -> WithEnv TermPlus
reduceTermPlus (m, TermEpsilonElim (x, t) e branchList) = do
  e' <- reduceTermPlus e
  case e' of
    (_, TermEpsilonIntro l _) ->
      case lookup (CaseLabel l) branchList of
        Just body -> reduceTermPlus $ substTermPlus [(x, e')] body
        Nothing ->
          case lookup CaseDefault branchList of
            Just body -> reduceTermPlus $ substTermPlus [(x, e')] body
            Nothing -> return (m, TermEpsilonElim (x, t) e' branchList)
    _ -> return (m, TermEpsilonElim (x, t) e' branchList)
reduceTermPlus (m, TermPiElim e es) = do
  e' <- reduceTermPlus e
  es' <- mapM reduceTermPlus es
  case e' of
    (_, TermPiIntro xts body)
      | length xts == length es'
      , all isValue es' -> do
        let xs = map fst xts
        reduceTermPlus $ substTermPlus (zip xs es') body
    self@(_, TermMu (x, _) body)
      | all isValue es' -> do
        let self' = substTermPlus [(x, self)] body
        reduceTermPlus (m, TermPiElim self' es')
    (_, TermTheta constant)
      | [(_, TermInt x t1), (_, TermInt y _)] <- es' -> do
        let b1 = constant `elem` intAddConstantList
        let b2 = constant `elem` intSubConstantList
        let b3 = constant `elem` intMulConstantList
        let b4 = constant `elem` intDivConstantList
        case (b1, b2, b3, b4) of
          (True, _, _, _) -> return (m, TermInt (x + y) t1)
          (_, True, _, _) -> return (m, TermInt (x - y) t1)
          (_, _, True, _) -> return (m, TermInt (x * y) t1)
          (_, _, _, True) -> return (m, TermInt (x `div` y) t1)
          _ -> return (m, TermPiElim e' es')
    (_, TermTheta constant)
      | [(_, TermFloat x t1), (_, TermFloat y _)] <- es' -> do
        let b1 = constant `elem` floatAddConstantList
        let b2 = constant `elem` floatSubConstantList
        let b3 = constant `elem` floatMulConstantList
        let b4 = constant `elem` floatDivConstantList
        case (b1, b2, b3, b4) of
          (True, _, _, _) -> return (m, TermFloat (x + y) t1)
          (_, True, _, _) -> return (m, TermFloat (x - y) t1)
          (_, _, True, _) -> return (m, TermFloat (x * y) t1)
          (_, _, _, True) -> return (m, TermFloat (x / y) t1)
          _ -> return (m, TermPiElim e' es')
    _ -> return (m, TermPiElim e' es')
reduceTermPlus t = return t
