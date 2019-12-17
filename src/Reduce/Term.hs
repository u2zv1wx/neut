module Reduce.Term
  ( reduceTermPlus
  ) where

import Unsafe.Coerce -- for int -> word, word -> int

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
      | [(_, TermInt x _), (_, TermInt y _)] <- es'
      , [typeStr, opStr] <- wordsBy '.' constant
      , Just t@(LowTypeSignedInt _) <- asLowTypeMaybe typeStr
      , Just arith <- asBinOpMaybe opStr -> do
        case arith of
          BinOpAdd -> return (m, TermInt (x + y) t)
          BinOpSub -> return (m, TermInt (x - y) t)
          BinOpMul -> return (m, TermInt (x * y) t)
          BinOpDiv -> return (m, TermInt (x `div` y) t)
          _ -> return (m, TermPiElim e' es')
    (_, TermTheta constant)
      | [(_, TermInt x _), (_, TermInt y _)] <- es'
      , [typeStr, opStr] <- wordsBy '.' constant
      , Just t@(LowTypeUnsignedInt _) <- asLowTypeMaybe typeStr
      , Just arith <- asBinOpMaybe opStr -> do
        case arith of
          BinOpAdd -> return (m, TermInt (x + y) t)
          BinOpSub -> return (m, TermInt (x - y) t)
          BinOpMul -> return (m, TermInt (x * y) t)
          BinOpDiv -> do
            let x' = unsafeCoerce x :: Word
            let y' = unsafeCoerce y :: Word
            let z = x' `div` y'
            return (m, TermInt (unsafeCoerce z) t)
          _ -> return (m, TermPiElim e' es')
    (_, TermTheta constant)
      | [(_, TermFloat x _), (_, TermFloat y _)] <- es'
      , [typeStr, opStr] <- wordsBy '.' constant
      , Just t@(LowTypeFloat _) <- asLowTypeMaybe typeStr
      , Just arith <- asBinOpMaybe opStr -> do
        case arith of
          BinOpAdd -> return (m, TermFloat (x + y) t)
          BinOpSub -> return (m, TermFloat (x - y) t)
          BinOpMul -> return (m, TermFloat (x * y) t)
          BinOpDiv -> return (m, TermFloat (x / y) t)
          _ -> return (m, TermPiElim e' es')
    _ -> return (m, TermPiElim e' es')
reduceTermPlus t = return t
