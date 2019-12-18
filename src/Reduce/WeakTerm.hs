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
      | [(_, WeakTermInt x)] <- es'
      , Just (LowTypeSignedInt _, op) <- asUnaryOpMaybe constant -> do
        case op of
          UnaryOpTrunc _ -> undefined
          UnaryOpZext _ -> return (m, WeakTermInt x)
          UnaryOpSext _ -> undefined
          UnaryOpTo (LowTypeFloat _) ->
            return (m, WeakTermFloat64 (fromIntegral x))
          _ -> return (m, WeakTermPiElim e' es')
    (_, WeakTermTheta constant)
      | [(_, WeakTermInt x)] <- es'
      , Just (LowTypeUnsignedInt _, op) <- asUnaryOpMaybe constant -> do
        case op of
          UnaryOpTrunc _ -> undefined
          UnaryOpZext _ -> return (m, WeakTermInt x)
          UnaryOpSext _ -> undefined
          UnaryOpTo (LowTypeFloat _) ->
            return (m, WeakTermFloat64 (fromIntegral x))
          _ -> return (m, WeakTermPiElim e' es')
    (_, WeakTermTheta constant)
      | [(_, WeakTermFloat64 x)] <- es'
      , Just (LowTypeFloat _, op) <- asUnaryOpMaybe constant ->
        case op of
          UnaryOpNeg -> return (m, WeakTermFloat64 (-x))
          UnaryOpTrunc _ -> undefined
          UnaryOpFpExt _ -> undefined
          UnaryOpTo _ -> undefined
          _ -> return (m, WeakTermPiElim e' es')
    (_, WeakTermTheta constant)
      | [(_, WeakTermInt x), (_, WeakTermInt y)] <- es'
      , Just (LowTypeSignedInt _, op) <- asBinaryOpMaybe constant ->
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
      , Just (LowTypeUnsignedInt _, op) <- asBinaryOpMaybe constant -> do
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
      | [(_, WeakTermFloat64 x), (_, WeakTermFloat64 y)] <- es'
      , Just (LowTypeFloat _, op) <- asBinaryOpMaybe constant ->
        case op of
          BinaryOpAdd -> return (m, WeakTermFloat64 (x + y))
          BinaryOpSub -> return (m, WeakTermFloat64 (x - y))
          BinaryOpMul -> return (m, WeakTermFloat64 (x * y))
          BinaryOpDiv -> return (m, WeakTermFloat64 (x / y))
          BinaryOpRem -> return (m, WeakTermFloat64 (x `mod'` y))
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
