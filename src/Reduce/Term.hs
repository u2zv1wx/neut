module Reduce.Term
  ( reduceTermPlus
  ) where

import Data.Bits
import Data.Fixed (mod')
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
      | [(_, TermFloat x t)] <- es'
      , [typeStr, opStr] <- wordsBy '.' constant
      , Just (LowTypeFloat _) <- asLowTypeMaybe typeStr
      , Just op <- asUnaryOpMaybe opStr
      , op == UnaryOpNeg -> return (m, TermFloat (-x) t)
    (_, TermTheta constant)
      | [(_, TermInt x _), (_, TermInt y _)] <- es'
      , [typeStr, opStr] <- wordsBy '.' constant
      , Just t@(LowTypeSignedInt _) <- asLowTypeMaybe typeStr
      , Just op <- asBinaryOpMaybe opStr -> do
        case op of
          BinaryOpAdd -> return (m, TermInt (x + y) t)
          BinaryOpSub -> return (m, TermInt (x - y) t)
          BinaryOpMul -> return (m, TermInt (x * y) t)
          BinaryOpDiv -> return (m, TermInt (x `div` y) t)
          BinaryOpRem -> return (m, TermInt (x `rem` y) t)
          BinaryOpEQ -> return (m, asEpsilon t $ x == y)
          BinaryOpNE -> return (m, asEpsilon t $ x /= y)
          BinaryOpGT -> return (m, asEpsilon t $ x > y)
          BinaryOpGE -> return (m, asEpsilon t $ x >= y)
          BinaryOpLT -> return (m, asEpsilon t $ x < y)
          BinaryOpLE -> return (m, asEpsilon t $ x <= y)
          BinaryOpShl -> return (m, TermInt (shiftL x y) t)
          BinaryOpLshr -> return (m, TermInt (ushiftR x y) t)
          BinaryOpAshr -> return (m, TermInt (shiftR x y) t)
    (_, TermTheta constant)
      | [(_, TermInt x _), (_, TermInt y _)] <- es'
      , [typeStr, opStr] <- wordsBy '.' constant
      , Just t@(LowTypeUnsignedInt _) <- asLowTypeMaybe typeStr
      , Just op <- asBinaryOpMaybe opStr -> do
        let x' = unsafeCoerce x :: Word
        let y' = unsafeCoerce y :: Word
        case op of
          BinaryOpAdd -> return (m, TermInt (x + y) t)
          BinaryOpSub -> return (m, TermInt (x - y) t)
          BinaryOpMul -> return (m, TermInt (x * y) t)
          BinaryOpDiv -> return (m, TermInt (unsafeCoerce (x' `div` y')) t)
          BinaryOpRem -> return (m, TermInt (unsafeCoerce (x' `rem` y')) t)
          BinaryOpEQ -> return (m, asEpsilon t $ x' == y')
          BinaryOpNE -> return (m, asEpsilon t $ x' /= y')
          BinaryOpGT -> return (m, asEpsilon t $ x' > y')
          BinaryOpGE -> return (m, asEpsilon t $ x' >= y')
          BinaryOpLT -> return (m, asEpsilon t $ x' < y')
          BinaryOpLE -> return (m, asEpsilon t $ x' <= y')
          BinaryOpShl -> return (m, TermInt (shiftL x y) t)
          BinaryOpLshr -> return (m, TermInt (ushiftR x y) t)
          BinaryOpAshr -> return (m, TermInt (shiftR x y) t)
    (_, TermTheta constant)
      | [(_, TermFloat x _), (_, TermFloat y _)] <- es'
      , [typeStr, opStr] <- wordsBy '.' constant
      , Just t@(LowTypeFloat _) <- asLowTypeMaybe typeStr
      , Just op <- asBinaryOpMaybe opStr -> do
        case op of
          BinaryOpAdd -> return (m, TermFloat (x + y) t)
          BinaryOpSub -> return (m, TermFloat (x - y) t)
          BinaryOpMul -> return (m, TermFloat (x * y) t)
          BinaryOpDiv -> return (m, TermFloat (x / y) t)
          BinaryOpRem -> return (m, TermFloat (x `mod'` y) t)
          BinaryOpEQ -> return (m, asEpsilon t $ x == y)
          BinaryOpNE -> return (m, asEpsilon t $ x /= y)
          BinaryOpGT -> return (m, asEpsilon t $ x > y)
          BinaryOpGE -> return (m, asEpsilon t $ x >= y)
          BinaryOpLT -> return (m, asEpsilon t $ x < y)
          BinaryOpLE -> return (m, asEpsilon t $ x <= y)
          _ -> return (m, TermPiElim e' es')
    _ -> return (m, TermPiElim e' es')
reduceTermPlus t = return t

asEpsilon :: LowType -> Bool -> Term
asEpsilon t True = TermEpsilonIntro "true" t
asEpsilon t False = TermEpsilonIntro "false" t
