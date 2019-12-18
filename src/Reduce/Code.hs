module Reduce.Code
  ( reduceCodePlus
  ) where

import Control.Monad.State
import Data.Bits
import Data.Fixed (mod')
import Unsafe.Coerce -- for int -> word, word -> int

import Data.Basic
import Data.Code
import Data.Env

reduceCodePlus :: CodePlus -> WithEnv CodePlus
reduceCodePlus (m, CodeEpsilonElim v branchList) =
  case v of
    (_, DataEpsilonIntro l) ->
      case lookup (CaseLabel l) branchList of
        Just body -> reduceCodePlus body
        Nothing ->
          case lookup CaseDefault branchList of
            Just body -> reduceCodePlus body
            Nothing -> return (m, CodeEpsilonElim v branchList)
    _ -> return (m, CodeEpsilonElim v branchList)
reduceCodePlus (m, CodePiElimDownElim v ds) = do
  cenv <- gets codeEnv
  case v of
    (_, DataTheta x)
      | Just (xs, body) <- lookup x cenv ->
        reduceCodePlus $ substCodePlus (zip xs ds) body
    _ -> return (m, CodePiElimDownElim v ds)
reduceCodePlus (m, CodeSigmaElim xs v e) =
  case v of
    (_, DataSigmaIntro es)
      | length es == length xs -> reduceCodePlus $ substCodePlus (zip xs es) e
    _ -> return (m, CodeSigmaElim xs v e)
reduceCodePlus (m, CodeTheta theta) =
  case theta of
    ThetaUnaryOp op (LowTypeFloat _) (m1, DataFloat64 x)
      | op == UnaryOpNeg -> upIntroData m (m1, DataFloat64 (-x))
    ThetaBinaryOp op t@(LowTypeSignedInt _) (m1, DataInt x _) (_, DataInt y _) -> do
      case op of
        BinaryOpAdd -> upIntroData m (m1, DataInt (x + y) t)
        BinaryOpSub -> upIntroData m (m1, DataInt (x - y) t)
        BinaryOpMul -> upIntroData m (m1, DataInt (x * y) t)
        BinaryOpDiv -> upIntroData m (m1, DataInt (x `div` y) t)
        BinaryOpRem -> upIntroData m (m1, DataInt (x `rem` y) t)
        BinaryOpEQ -> upIntroData m (m1, asData $ x == y)
        BinaryOpNE -> upIntroData m (m1, asData $ x /= y)
        BinaryOpGT -> upIntroData m (m1, asData $ x > y)
        BinaryOpGE -> upIntroData m (m1, asData $ x >= y)
        BinaryOpLT -> upIntroData m (m1, asData $ x < y)
        BinaryOpLE -> upIntroData m (m1, asData $ x <= y)
        BinaryOpShl -> upIntroData m (m1, DataInt (shiftL x y) t)
        BinaryOpLshr -> upIntroData m (m1, DataInt (ushiftR x y) t)
        BinaryOpAshr -> upIntroData m (m1, DataInt (shiftR x y) t)
        BinaryOpAnd -> upIntroData m (m1, DataInt (x .&. y) t)
        BinaryOpOr -> upIntroData m (m1, DataInt (x .|. y) t)
        BinaryOpXor -> upIntroData m (m1, DataInt (x `xor` y) t)
    ThetaBinaryOp op t@(LowTypeUnsignedInt _) (m1, DataInt x _) (_, DataInt y _) -> do
      let x' = unsafeCoerce x :: Word
      let y' = unsafeCoerce y :: Word
      case op of
        BinaryOpAdd -> upIntroData m (m1, DataInt (x + y) t)
        BinaryOpSub -> upIntroData m (m1, DataInt (x - y) t)
        BinaryOpMul -> upIntroData m (m1, DataInt (x * y) t)
        BinaryOpDiv ->
          upIntroData m (m1, DataInt (unsafeCoerce (x' `div` y')) t)
        BinaryOpRem ->
          upIntroData m (m1, DataInt (unsafeCoerce (x' `rem` y')) t)
        BinaryOpEQ -> upIntroData m (m1, asData $ x' == y')
        BinaryOpNE -> upIntroData m (m1, asData $ x' /= y')
        BinaryOpGT -> upIntroData m (m1, asData $ x' > y')
        BinaryOpGE -> upIntroData m (m1, asData $ x' >= y')
        BinaryOpLT -> upIntroData m (m1, asData $ x' < y')
        BinaryOpLE -> upIntroData m (m1, asData $ x' <= y')
        BinaryOpShl -> upIntroData m (m1, DataInt (shiftL x y) t)
        BinaryOpLshr -> upIntroData m (m1, DataInt (ushiftR x y) t)
        BinaryOpAshr -> upIntroData m (m1, DataInt (shiftR x y) t)
        BinaryOpAnd -> upIntroData m (m1, DataInt (x .&. y) t)
        BinaryOpOr -> upIntroData m (m1, DataInt (x .|. y) t)
        BinaryOpXor -> upIntroData m (m1, DataInt (x `xor` y) t)
    ThetaBinaryOp op (LowTypeFloat _) (m1, DataFloat16 x) (_, DataFloat16 y) -> do
      case computeFloat x y op of
        Just (Left d) -> upIntroData m (m1, d)
        Just (Right z) -> upIntroData m (m1, DataFloat16 z)
        Nothing -> return (m, CodeTheta theta)
    ThetaBinaryOp op (LowTypeFloat _) (m1, DataFloat32 x) (_, DataFloat32 y) -> do
      case computeFloat x y op of
        Just (Left d) -> upIntroData m (m1, d)
        Just (Right z) -> upIntroData m (m1, DataFloat32 z)
        Nothing -> return (m, CodeTheta theta)
    ThetaBinaryOp op (LowTypeFloat _) (m1, DataFloat64 x) (_, DataFloat64 y) -> do
      case computeFloat x y op of
        Just (Left d) -> upIntroData m (m1, d)
        Just (Right z) -> upIntroData m (m1, DataFloat64 z)
        Nothing -> return (m, CodeTheta theta)
    ThetaPrint (_, DataInt i _) -> do
      liftIO $ putStr $ show i
      return (m, CodeUpIntro (Nothing, DataSigmaIntro []))
    _ -> return (m, CodeTheta theta)
reduceCodePlus t = return t

computeFloat ::
     (Real a, Fractional a) => a -> a -> BinaryOp -> Maybe (Either Data a)
computeFloat x y BinaryOpAdd = Just $ Right $ x + y
computeFloat x y BinaryOpSub = Just $ Right $ x - y
computeFloat x y BinaryOpMul = Just $ Right $ x * y
computeFloat x y BinaryOpDiv = Just $ Right $ x / y
computeFloat x y BinaryOpRem = Just $ Right $ x `mod'` y
computeFloat x y BinaryOpEQ = Just $ Left $ asData $ x == y
computeFloat x y BinaryOpNE = Just $ Left $ asData $ x /= y
computeFloat x y BinaryOpGT = Just $ Left $ asData $ x > y
computeFloat x y BinaryOpGE = Just $ Left $ asData $ x >= y
computeFloat x y BinaryOpLT = Just $ Left $ asData $ x < y
computeFloat x y BinaryOpLE = Just $ Left $ asData $ x <= y
computeFloat _ _ _ = Nothing

asData :: Bool -> Data
asData True = DataInt 1 (LowTypeSignedInt 64) -- epsilon ~> i64
asData False = DataInt 0 (LowTypeSignedInt 64)

upIntroData :: Monad m => a -> DataPlus -> m (a, Code)
upIntroData m d = return (m, CodeUpIntro d)
