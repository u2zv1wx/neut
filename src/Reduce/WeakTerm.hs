module Reduce.WeakTerm
  ( reduceWeakTermPlus
  ) where

import Data.Bits
import Data.Fixed (mod')
import Unsafe.Coerce -- for int -> word, word -> int

import Data.Basic
import Data.Env
import Data.WeakTerm

reduceWeakTermPlus :: WeakTermPlus -> WithEnv WeakTermPlus
reduceWeakTermPlus (m, WeakTermEpsilonElim (x, t) e branchList) = do
  e' <- reduceWeakTermPlus e
  case e' of
    (_, WeakTermEpsilonIntro l) ->
      case lookup (CaseLabel l) branchList of
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
      | [(_, WeakTermFloat x)] <- es'
      , [typeStr, opStr] <- wordsBy '.' constant
      , Just (LowTypeFloat _) <- asLowTypeMaybe typeStr
      , Just op <- asUnaryOpMaybe opStr
      , op == UnaryOpNeg -> return (m, WeakTermFloat (-x))
    (_, WeakTermTheta constant)
      | [(_, WeakTermInt x), (_, WeakTermInt y)] <- es'
      , [typeStr, opStr] <- wordsBy '.' constant
      , Just (LowTypeSignedInt _) <- asLowTypeMaybe typeStr
      , Just op <- asBinaryOpMaybe opStr -> do
        case op of
          BinaryOpAdd -> return (m, WeakTermInt (x + y))
          BinaryOpSub -> return (m, WeakTermInt (x - y))
          BinaryOpMul -> return (m, WeakTermInt (x * y))
          BinaryOpDiv -> return (m, WeakTermInt (x `div` y))
          BinaryOpRem -> return (m, WeakTermInt (x `rem` y))
          BinaryOpEQ -> return (m, asEpsilon $ x == y)
          BinaryOpNE -> return (m, asEpsilon $ x /= y)
          BinaryOpGT -> return (m, asEpsilon $ x > y)
          BinaryOpGE -> return (m, asEpsilon $ x >= y)
          BinaryOpLT -> return (m, asEpsilon $ x < y)
          BinaryOpLE -> return (m, asEpsilon $ x <= y)
          BinaryOpShl -> return (m, WeakTermInt (shiftL x y))
          BinaryOpLshr -> return (m, WeakTermInt (ushiftR x y))
          BinaryOpAshr -> return (m, WeakTermInt (shiftR x y))
          BinaryOpAnd -> return (m, WeakTermInt (x .&. y))
          BinaryOpOr -> return (m, WeakTermInt (x .|. y))
          BinaryOpXor -> return (m, WeakTermInt (x `xor` y))
    (_, WeakTermTheta constant)
      | [(_, WeakTermInt x), (_, WeakTermInt y)] <- es'
      , [typeStr, opStr] <- wordsBy '.' constant
      , Just (LowTypeUnsignedInt _) <- asLowTypeMaybe typeStr
      , Just op <- asBinaryOpMaybe opStr -> do
        let x' = unsafeCoerce x :: Word
        let y' = unsafeCoerce y :: Word
        case op of
          BinaryOpAdd -> return (m, WeakTermInt (unsafeCoerce $ x' + y'))
          BinaryOpSub -> return (m, WeakTermInt (unsafeCoerce $ x' - y'))
          BinaryOpMul -> return (m, WeakTermInt (unsafeCoerce $ x' * y'))
          BinaryOpDiv -> return (m, WeakTermInt (unsafeCoerce (x' `div` y')))
          BinaryOpRem -> return (m, WeakTermInt (unsafeCoerce $ x' `rem` y'))
          BinaryOpEQ -> return (m, asEpsilon $ x' == y')
          BinaryOpNE -> return (m, asEpsilon $ x' /= y')
          BinaryOpGT -> return (m, asEpsilon $ x' > y')
          BinaryOpGE -> return (m, asEpsilon $ x' >= y')
          BinaryOpLT -> return (m, asEpsilon $ x' < y')
          BinaryOpLE -> return (m, asEpsilon $ x' <= y')
          BinaryOpShl -> return (m, WeakTermInt (shiftL x y))
          BinaryOpLshr -> return (m, WeakTermInt (ushiftR x y))
          BinaryOpAshr -> return (m, WeakTermInt (shiftR x y))
          BinaryOpAnd -> return (m, WeakTermInt (x .&. y))
          BinaryOpOr -> return (m, WeakTermInt (x .|. y))
          BinaryOpXor -> return (m, WeakTermInt (x `xor` y))
    (_, WeakTermTheta constant)
      | [(_, WeakTermFloat x), (_, WeakTermFloat y)] <- es'
      , [typeStr, opStr] <- wordsBy '.' constant
      , Just (LowTypeFloat _) <- asLowTypeMaybe typeStr
      , Just op <- asBinaryOpMaybe opStr -> do
        case op of
          BinaryOpAdd -> return (m, WeakTermFloat (x + y))
          BinaryOpSub -> return (m, WeakTermFloat (x - y))
          BinaryOpMul -> return (m, WeakTermFloat (x * y))
          BinaryOpDiv -> return (m, WeakTermFloat (x / y))
          BinaryOpRem -> return (m, WeakTermFloat (x `mod'` y))
          BinaryOpEQ -> return (m, asEpsilon $ x == y)
          BinaryOpNE -> return (m, asEpsilon $ x /= y)
          BinaryOpGT -> return (m, asEpsilon $ x > y)
          BinaryOpGE -> return (m, asEpsilon $ x >= y)
          BinaryOpLT -> return (m, asEpsilon $ x < y)
          BinaryOpLE -> return (m, asEpsilon $ x <= y)
          _ -> return (m, WeakTermPiElim e' es')
    _ -> return (m, WeakTermPiElim e' es')
reduceWeakTermPlus t = return t

asEpsilon :: Bool -> WeakTerm
asEpsilon True = WeakTermEpsilonIntro "true"
asEpsilon False = WeakTermEpsilonIntro "false"
