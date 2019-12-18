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
reduceTermPlus (m, TermEpsilonElim e branchList) = do
  e' <- reduceTermPlus e
  case e' of
    (_, TermEpsilonIntro l) ->
      case lookup (CaseLabel l) branchList of
        Just body -> reduceTermPlus body
        Nothing ->
          case lookup CaseDefault branchList of
            Just body -> reduceTermPlus body
            Nothing -> return (m, TermEpsilonElim e' branchList)
    _ -> return (m, TermEpsilonElim e' branchList)
reduceTermPlus (m, TermPiElim e es) = do
  e' <- reduceTermPlus e
  es' <- mapM reduceTermPlus es
  let app = TermPiElim e' es'
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
      | [(_, TermFloat64 x)] <- es'
      , Just (LowTypeFloat _, op) <- asUnaryOpMaybe constant ->
        case op of
          UnaryOpNeg -> return (m, TermFloat64 (-x))
          _ -> return (m, app)
    (_, TermTheta constant)
      | [(_, TermInt x _), (_, TermInt y _)] <- es'
      , Just (t@(LowTypeSignedInt _), op) <- asBinaryOpMaybe constant ->
        case computeInt x y op of
          Left b -> return (m, b)
          Right i -> return (m, TermInt i t)
    (_, TermTheta constant)
      | [(_, TermInt x _), (_, TermInt y _)] <- es'
      , Just (t@(LowTypeUnsignedInt _), op) <- asBinaryOpMaybe constant -> do
        let x' = unsafeCoerce x :: Word
        let y' = unsafeCoerce y :: Word
        case computeInt x' y' op of
          Left b -> return (m, b)
          Right i -> return (m, TermInt (unsafeCoerce i) t)
    (_, TermTheta constant)
      | [(_, TermFloat16 x), (_, TermFloat16 y)] <- es'
      , Just ((LowTypeFloat FloatSize16), op) <- asBinaryOpMaybe constant ->
        case computeFloat x y op app of
          Left b -> return (m, b)
          Right z -> return (m, TermFloat16 z)
    (_, TermTheta constant)
      | [(_, TermFloat32 x), (_, TermFloat32 y)] <- es'
      , Just ((LowTypeFloat FloatSize32), op) <- asBinaryOpMaybe constant ->
        case computeFloat x y op app of
          Left b -> return (m, b)
          Right z -> return (m, TermFloat32 z)
    (_, TermTheta constant)
      | [(_, TermFloat64 x), (_, TermFloat64 y)] <- es'
      , Just ((LowTypeFloat FloatSize64), op) <- asBinaryOpMaybe constant ->
        case computeFloat x y op app of
          Left b -> return (m, b)
          Right z -> return (m, TermFloat64 z)
    _ -> return (m, app)
reduceTermPlus t = return t

computeInt :: (Integral a, Bits a) => a -> a -> BinaryOp -> Either Term a
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
     (Real a, Fractional a) => a -> a -> BinaryOp -> Term -> Either Term a
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

asEpsilon :: Bool -> Term
asEpsilon True = TermEpsilonIntro "true"
asEpsilon False = TermEpsilonIntro "false"
