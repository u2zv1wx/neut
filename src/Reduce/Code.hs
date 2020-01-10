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
reduceCodePlus (m, CodePiElimDownElim v ds) = do
  cenv <- gets codeEnv
  case v of
    (_, DataTheta x)
      | Just (xs, body) <- lookup x cenv
      , x `notElem` varCode body
      , length xs == length ds ->
        reduceCodePlus $ substCodePlus (zip xs ds) body
    (_, DataTheta x)
      | Just (xs, body) <- lookup x cenv
      , x `notElem` varCode body -> error "length unmatch"
    _ -> return (m, CodePiElimDownElim v ds)
reduceCodePlus (m, CodeSigmaElim xts v e) = do
  let (xs, ts) = unzip xts
  -- let xs = map fst xts
  case v of
    (_, DataSigmaIntro es)
      | length es == length xs -> reduceCodePlus $ substCodePlus (zip xs es) e
    _ -> do
      e' <- reduceCodePlus e
      ts' <- mapM reduceCodePlus ts
      return (m, CodeSigmaElim (zip xs ts') v e')
reduceCodePlus (m, CodeUpElim x e1 e2) = do
  e1' <- reduceCodePlus e1
  case e1' of
    (_, CodeUpIntro d) -> reduceCodePlus $ substCodePlus [(x, d)] e2
    _ -> do
      e2' <- reduceCodePlus e2
      return (m, CodeUpElim x e1' e2')
reduceCodePlus (m, CodeEnumElim v les) = do
  let (ls, es) = unzip les
  es' <- mapM reduceCodePlus es
  case v of
    (_, DataEnumIntro l) ->
      case lookup (CaseValue l) les of
        Just body -> reduceCodePlus body
        Nothing ->
          case lookup CaseDefault les of
            Just body -> reduceCodePlus body
            Nothing -> return (m, CodeEnumElim v $ zip ls es')
    _ -> do
      return (m, CodeEnumElim v $ zip ls es')
reduceCodePlus (m, CodeArrayElim k d1 d2) = do
  case (d1, d2) of
    ((_, DataArrayIntro k' les), (_, DataEnumIntro l))
      | k == k'
      , Just d <- lookup l les -> return (m, CodeUpIntro d)
    _ -> return (m, CodeArrayElim k d1 d2)
reduceCodePlus (m, CodeTheta theta) =
  case theta of
    ThetaUnaryOp op (LowTypeIntS s) (m1, DataIntS s1 x)
      | s == s1 ->
        case op of
          UnaryOpTrunc (LowTypeIntS s2)
            | s1 > s2 -> upIntroData m (m1, DataIntS s2 (x .&. (2 ^ s2 - 1)))
          UnaryOpZext (LowTypeIntS s2)
            | s1 < s2 -> do
              let s1' = toInteger s1
              let s2' = toInteger s2
              upIntroData m (m1, DataIntS s2 (asIntS s2' (asIntU s1' x)))
          UnaryOpSext (LowTypeIntS s2)
            | s1 < s2 -> upIntroData m (m1, DataIntS s2 x)
          UnaryOpTo (LowTypeFloat FloatSize16) ->
            upIntroData m (m1, DataFloat16 (fromIntegral x))
          UnaryOpTo (LowTypeFloat FloatSize32) ->
            upIntroData m (m1, DataFloat32 (fromIntegral x))
          UnaryOpTo (LowTypeFloat FloatSize64) ->
            upIntroData m (m1, DataFloat64 (fromIntegral x))
          _ -> return (m, CodeTheta theta)
    ThetaUnaryOp op (LowTypeIntU s) (m1, DataIntU s1 x)
      | s == s1 ->
        case op of
          UnaryOpTrunc (LowTypeIntU s2)
            | s1 > s2 -> upIntroData m (m1, DataIntU s2 (x .&. (2 ^ s2 - 1)))
          UnaryOpZext (LowTypeIntU s2)
            | s1 < s2 -> upIntroData m (m1, DataIntU s2 x)
          UnaryOpSext (LowTypeIntU s2)
            | s1 < s2 -> do
              let s1' = toInteger s1
              let s2' = toInteger s2
              upIntroData m (m1, DataIntU s2 (asIntU s2' (asIntS s1' x)))
          UnaryOpTo (LowTypeFloat FloatSize16) ->
            upIntroData m (m1, DataFloat16 (fromIntegral x))
          UnaryOpTo (LowTypeFloat FloatSize32) ->
            upIntroData m (m1, DataFloat32 (fromIntegral x))
          UnaryOpTo (LowTypeFloat FloatSize64) ->
            upIntroData m (m1, DataFloat64 (fromIntegral x))
          _ -> return (m, CodeTheta theta)
    ThetaUnaryOp op (LowTypeFloat FloatSize16) (m1, DataFloat16 x) ->
      case op of
        UnaryOpNeg -> upIntroData m (m1, DataFloat16 (-x))
        UnaryOpFpExt (LowTypeFloat FloatSize32) ->
          upIntroData m (m1, DataFloat32 (realToFrac x))
        UnaryOpFpExt (LowTypeFloat FloatSize64) ->
          upIntroData m (m1, DataFloat64 (realToFrac x))
        UnaryOpTo (LowTypeIntS s) -> do
          let s' = toInteger s
          upIntroData m (m1, DataIntS s (asIntS s' (round x)))
        UnaryOpTo (LowTypeIntU s) -> do
          let s' = toInteger s
          upIntroData m (m1, DataIntU s (asIntU s' (round x)))
        _ -> return (m, CodeTheta theta)
    ThetaUnaryOp op (LowTypeFloat FloatSize32) (m1, DataFloat32 x) ->
      case op of
        UnaryOpNeg -> upIntroData m (m1, DataFloat32 (-x))
        UnaryOpTrunc (LowTypeFloat FloatSize16) ->
          upIntroData m (m1, DataFloat16 (realToFrac x))
        UnaryOpFpExt (LowTypeFloat FloatSize64) ->
          upIntroData m (m1, DataFloat64 (realToFrac x))
        UnaryOpTo (LowTypeIntS s) -> do
          let s' = toInteger s
          upIntroData m (m1, DataIntS s (asIntS s' (round x)))
        UnaryOpTo (LowTypeIntU s) -> do
          let s' = toInteger s
          upIntroData m (m1, DataIntU s (asIntU s' (round x)))
        _ -> return (m, CodeTheta theta)
    ThetaUnaryOp op (LowTypeFloat FloatSize64) (m1, DataFloat64 x) ->
      case op of
        UnaryOpNeg -> upIntroData m (m1, DataFloat64 (-x))
        UnaryOpTrunc (LowTypeFloat FloatSize16) ->
          upIntroData m (m1, DataFloat16 (realToFrac x))
        UnaryOpTrunc (LowTypeFloat FloatSize32) ->
          upIntroData m (m1, DataFloat32 (realToFrac x))
        UnaryOpTo (LowTypeIntS s) -> do
          let s' = toInteger s
          upIntroData m (m1, DataIntS s (asIntS s' (round x)))
        UnaryOpTo (LowTypeIntU s) -> do
          let s' = toInteger s
          upIntroData m (m1, DataIntU s (asIntU s' (round x)))
        _ -> return (m, CodeTheta theta)
    ThetaBinaryOp op (LowTypeIntS s) (m1, DataIntS s1 x) (_, DataIntS s2 y)
      | s == s1 && s == s2 -> do
        case computeInt asIntS (toInteger s) x y op of
          Left d -> upIntroData m (m1, d)
          Right z -> upIntroData m (m1, DataIntS s z)
    ThetaBinaryOp op (LowTypeIntU s) (m1, DataIntU s1 x) (_, DataIntU s2 y)
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
