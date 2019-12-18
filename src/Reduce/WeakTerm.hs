module Reduce.WeakTerm
  ( reduceWeakTermPlus
  ) where

import Data.Bits
import Data.Fixed (mod')
import Numeric.Half
import Unsafe.Coerce -- for int -> word, word -> int

import Data.Basic
import Data.Env
import Data.WeakTerm

reduceWeakTermPlus :: WeakTermPlus -> WithEnv WeakTermPlus
reduceWeakTermPlus (m, WeakTermEpsilonElim e branchList) = do
  e' <- reduceWeakTermPlus e
  case e' of
    (_, WeakTermEpsilonIntro l) ->
      case lookup (CaseLabel l) branchList of
        Just body -> reduceWeakTermPlus body
        Nothing ->
          case lookup CaseDefault branchList of
            Just body -> reduceWeakTermPlus body
            Nothing -> return (m, WeakTermEpsilonElim e' branchList)
    _ -> return (m, WeakTermEpsilonElim e' branchList)
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
        case computeInt x y op of
          Left b -> return (m, b)
          Right i -> return (m, WeakTermInt i)
    (_, WeakTermTheta constant)
      | [(_, WeakTermInt x), (_, WeakTermInt y)] <- es'
      , Just (LowTypeUnsignedInt _, op) <- asBinaryOpMaybe constant -> do
        let x' = unsafeCoerce x :: Word
        let y' = unsafeCoerce y :: Word
        case computeInt x' y' op of
          Left b -> return (m, b)
          Right i -> return (m, WeakTermInt $ unsafeCoerce i)
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
    (_, WeakTermTheta constant)
      | Just (x, y) <- anyPlusF16 es'
      , Just (LowTypeFloat FloatSize16, op) <- asBinaryOpMaybe constant -> do
        let x' = realToFrac x
        case computeFloat x' y op app of
          Left b -> return (m, b)
          Right z -> return (m, WeakTermFloat16 z)
    (_, WeakTermTheta constant)
      | Just (x, y) <- anyPlusF32 es'
      , Just (LowTypeFloat FloatSize32, op) <- asBinaryOpMaybe constant -> do
        let x' = realToFrac x
        case computeFloat x' y op app of
          Left b -> return (m, b)
          Right z -> return (m, WeakTermFloat32 z)
    (_, WeakTermTheta constant)
      | Just (x, y) <- anyPlusF64 es'
      , Just (LowTypeFloat FloatSize64, op) <- asBinaryOpMaybe constant -> do
        let x' = realToFrac x
        case computeFloat x' y op app of
          Left b -> return (m, b)
          Right z -> return (m, WeakTermFloat64 z)
    (_, WeakTermTheta constant)
      | Just (x, y) <- anyPlusAny es'
      , Just (LowTypeFloat FloatSize16, op) <- asBinaryOpMaybe constant -> do
        let x' = realToFrac x
        let y' = realToFrac y
        case computeFloat x' y' op app of
          Left b -> return (m, b)
          Right z -> return (m, WeakTermFloat16 z)
    (_, WeakTermTheta constant)
      | Just (x, y) <- anyPlusAny es'
      , Just (LowTypeFloat FloatSize32, op) <- asBinaryOpMaybe constant -> do
        let x' = realToFrac x
        let y' = realToFrac y
        case computeFloat x' y' op app of
          Left b -> return (m, b)
          Right z -> return (m, WeakTermFloat32 z)
    (_, WeakTermTheta constant)
      | Just (x, y) <- anyPlusAny es'
      , Just (LowTypeFloat FloatSize64, op) <- asBinaryOpMaybe constant -> do
        case computeFloat x y op app of
          Left b -> return (m, b)
          Right z -> return (m, WeakTermFloat64 z)
    _ -> return (m, app)
reduceWeakTermPlus t = return t

anyPlusF16 :: [WeakTermPlus] -> Maybe (Double, Half)
anyPlusF16 [(_, WeakTermFloatUnknown x), (_, WeakTermFloat16 y)] = Just (x, y)
anyPlusF16 [(_, WeakTermFloat16 x), (_, WeakTermFloatUnknown y)] = Just (y, x)
anyPlusF16 _ = Nothing

anyPlusF32 :: [WeakTermPlus] -> Maybe (Double, Float)
anyPlusF32 [(_, WeakTermFloatUnknown x), (_, WeakTermFloat32 y)] = Just (x, y)
anyPlusF32 [(_, WeakTermFloat32 x), (_, WeakTermFloatUnknown y)] = Just (y, x)
anyPlusF32 _ = Nothing

anyPlusF64 :: [WeakTermPlus] -> Maybe (Double, Double)
anyPlusF64 [(_, WeakTermFloatUnknown x), (_, WeakTermFloat64 y)] = Just (x, y)
anyPlusF64 [(_, WeakTermFloat64 x), (_, WeakTermFloatUnknown y)] = Just (y, x)
anyPlusF64 _ = Nothing

anyPlusAny :: [WeakTermPlus] -> Maybe (Double, Double)
anyPlusAny [(_, WeakTermFloatUnknown x), (_, WeakTermFloatUnknown y)] =
  Just (x, y)
anyPlusAny _ = Nothing

computeInt :: (Integral a, Bits a) => a -> a -> BinaryOp -> Either WeakTerm a
computeInt x y BinaryOpAdd = Right $ x + y
computeInt x y BinaryOpSub = Right $ x - y
computeInt x y BinaryOpMul = Right $ x * y
computeInt x y BinaryOpDiv = Right $ x `div` y
computeInt x y BinaryOpRem = Right $ x `rem` y
computeInt x y BinaryOpEQ = Left $ asEpsilon $ x == y
computeInt x y BinaryOpNE = Left $ asEpsilon $ x /= y
computeInt x y BinaryOpGT = Left $ asEpsilon $ x > y
computeInt x y BinaryOpGE = Left $ asEpsilon $ x >= y
computeInt x y BinaryOpLT = Left $ asEpsilon $ x < y
computeInt x y BinaryOpLE = Left $ asEpsilon $ x <= y
computeInt x y BinaryOpShl = Right $ shiftL x (unsafeCoerce y)
computeInt x y BinaryOpLshr = Right $ ushiftR' x (unsafeCoerce y)
computeInt x y BinaryOpAshr = Right $ shiftR x (unsafeCoerce y)
computeInt x y BinaryOpAnd = Right $ x .&. y
computeInt x y BinaryOpOr = Right $ x .|. y
computeInt x y BinaryOpXor = Right $ x `xor` y

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
