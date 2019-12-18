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
    ThetaBinaryOp op (LowTypeSignedInt s) (m1, DataIntS s1 x) (_, DataIntS s2 y)
      | s == s1 && s == s2 -> do
        case computeInt asIntS (toInteger s) x y op of
          Left d -> upIntroData m (m1, d)
          Right z -> upIntroData m (m1, DataIntS s z)
    ThetaBinaryOp op (LowTypeUnsignedInt s) (m1, DataIntU s1 x) (_, DataIntU s2 y)
      | s == s1 && s == s2 -> do
        case computeInt asIntU (toInteger s) x y op of
          Left d -> upIntroData m (m1, d)
          Right z -> upIntroData m (m1, DataIntS s z)
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
    ThetaPrint (_, DataIntS _ i) -> do
      liftIO $ putStr $ show i
      return (m, CodeUpIntro (Nothing, DataSigmaIntro []))
    _ -> return (m, CodeTheta theta)
reduceCodePlus t = return t

computeInt ::
     (Integral a, Bits a)
  => (a -> a -> a) -- asIntS or asIntU
  -> a
  -> a
  -> a
  -> BinaryOp
  -> Either Data a
computeInt k m x y BinaryOpAdd = Right $ k m $ x + y
computeInt k m x y BinaryOpSub = Right $ k m $ x - y
computeInt k m x y BinaryOpMul = Right $ k m $ x * y
computeInt k m x y BinaryOpDiv = Right $ k m $ x `div` y
computeInt k m x y BinaryOpRem = Right $ k m $ x `rem` y
computeInt _ _ x y BinaryOpEQ = Left $ asData $ x == y
computeInt _ _ x y BinaryOpNE = Left $ asData $ x /= y
computeInt _ _ x y BinaryOpGT = Left $ asData $ x > y
computeInt _ _ x y BinaryOpGE = Left $ asData $ x >= y
computeInt _ _ x y BinaryOpLT = Left $ asData $ x < y
computeInt _ _ x y BinaryOpLE = Left $ asData $ x <= y
computeInt k m x y BinaryOpShl = Right $ k m $ shiftL x (unsafeCoerce y)
computeInt k m x y BinaryOpLshr = Right $ k m $ ushiftR' x (unsafeCoerce y)
computeInt k m x y BinaryOpAshr = Right $ k m $ shiftR x (unsafeCoerce y)
computeInt _ _ x y BinaryOpAnd = Right $ x .&. y
computeInt _ _ x y BinaryOpOr = Right $ x .|. y
computeInt _ _ x y BinaryOpXor = Right $ x `xor` y

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
asData True = DataIntS 64 1
asData False = DataIntS 64 0

upIntroData :: Monad m => a -> DataPlus -> m (a, Code)
upIntroData m d = return (m, CodeUpIntro d)
