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
      case computeInt x y op of
        Left d -> upIntroData m (m1, d)
        Right z -> upIntroData m (m1, DataInt z t)
    ThetaBinaryOp op t@(LowTypeUnsignedInt _) (m1, DataInt x _) (_, DataInt y _) -> do
      let x' = unsafeCoerce x :: Word
      let y' = unsafeCoerce y :: Word
      case computeInt x' y' op of
        Left d -> upIntroData m (m1, d)
        Right z -> upIntroData m (m1, DataInt (unsafeCoerce z) t)
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

computeInt :: (Integral a, Bits a) => a -> a -> BinaryOp -> Either Data a
computeInt x y BinaryOpAdd = Right $ x + y
computeInt x y BinaryOpSub = Right $ x - y
computeInt x y BinaryOpMul = Right $ x * y
computeInt x y BinaryOpDiv = Right $ x `div` y
computeInt x y BinaryOpRem = Right $ x `rem` y
computeInt x y BinaryOpEQ = Left $ asData $ x == y
computeInt x y BinaryOpNE = Left $ asData $ x /= y
computeInt x y BinaryOpGT = Left $ asData $ x > y
computeInt x y BinaryOpGE = Left $ asData $ x >= y
computeInt x y BinaryOpLT = Left $ asData $ x < y
computeInt x y BinaryOpLE = Left $ asData $ x <= y
computeInt x y BinaryOpShl = Right $ shiftL x (unsafeCoerce y)
computeInt x y BinaryOpLshr = Right $ ushiftR' x (unsafeCoerce y)
computeInt x y BinaryOpAshr = Right $ shiftR x (unsafeCoerce y)
computeInt x y BinaryOpAnd = Right $ x .&. y
computeInt x y BinaryOpOr = Right $ x .|. y
computeInt x y BinaryOpXor = Right $ x `xor` y

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
