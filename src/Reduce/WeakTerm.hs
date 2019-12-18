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
  let app = WeakTermPiElim e' es'
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
          _ -> return (m, app)
    (_, WeakTermTheta constant)
      | [(_, WeakTermInt x)] <- es'
      , Just (LowTypeUnsignedInt _, op) <- asUnaryOpMaybe constant -> do
        case op of
          UnaryOpTrunc _ -> undefined
          UnaryOpZext _ -> return (m, WeakTermInt x)
          UnaryOpSext _ -> undefined
          UnaryOpTo (LowTypeFloat _) ->
            return (m, WeakTermFloat64 (fromIntegral x))
          _ -> return (m, app)
    (_, WeakTermTheta constant)
      | [(_, WeakTermFloat64 x)] <- es'
      , Just (LowTypeFloat _, op) <- asUnaryOpMaybe constant ->
        case op of
          UnaryOpNeg -> return (m, WeakTermFloat64 (-x))
          UnaryOpTrunc _ -> undefined
          UnaryOpFpExt _ -> undefined
          UnaryOpTo _ -> undefined
          _ -> return (m, app)
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
      | [(_, WeakTermFloat16 x), (_, WeakTermFloat16 y)] <- es'
      , Just (LowTypeFloat FloatSize16, op) <- asBinaryOpMaybe constant ->
        case computeFloat x y op app of
          Left b -> return (m, b)
          Right z -> return (m, WeakTermFloat16 z)
    (_, WeakTermTheta constant)
      | [(_, WeakTermFloat32 x), (_, WeakTermFloat32 y)] <- es'
      , Just (LowTypeFloat FloatSize32, op) <- asBinaryOpMaybe constant ->
        case computeFloat x y op app of
          Left b -> return (m, b)
          Right z -> return (m, WeakTermFloat32 z)
    (_, WeakTermTheta constant)
      | [(_, WeakTermFloat64 x), (_, WeakTermFloat64 y)] <- es'
      , Just (LowTypeFloat FloatSize64, op) <- asBinaryOpMaybe constant ->
        case computeFloat x y op app of
          Left b -> return (m, b)
          Right z -> return (m, WeakTermFloat64 z)
    _ -> return (m, app)
reduceWeakTermPlus t = return t

computeFloat ::
     (Real a, Fractional a)
  => a
  -> a
  -> BinaryOp
  -> WeakTerm
  -> Either WeakTerm a
computeFloat x y BinaryOpAdd _ = Right $ x + y
computeFloat x y BinaryOpSub _ = Right $ x - y
computeFloat x y BinaryOpMul _ = Right $ x * y
computeFloat x y BinaryOpDiv _ = Right $ x / y
computeFloat x y BinaryOpRem _ = Right $ x `mod'` y
computeFloat x y BinaryOpEQ _ = Left $ asEpsilon $ x == y
computeFloat x y BinaryOpNE _ = Left $ asEpsilon $ x /= y
computeFloat x y BinaryOpGT _ = Left $ asEpsilon $ x > y
computeFloat x y BinaryOpGE _ = Left $ asEpsilon $ x >= y
computeFloat x y BinaryOpLT _ = Left $ asEpsilon $ x < y
computeFloat x y BinaryOpLE _ = Left $ asEpsilon $ x <= y
computeFloat _ _ _ e = Left e

asEpsilon :: Bool -> WeakTerm
asEpsilon True = WeakTermEpsilonIntro "true"
asEpsilon False = WeakTermEpsilonIntro "false"
