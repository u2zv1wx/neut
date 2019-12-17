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
reduceCodePlus (m, CodeEpsilonElim (x, lowType) v branchList) =
  case v of
    (_, DataEpsilonIntro l _) ->
      case lookup (CaseLabel l) branchList of
        Just body -> reduceCodePlus $ substCodePlus [(x, v)] body
        Nothing ->
          case lookup CaseDefault branchList of
            Just body -> reduceCodePlus $ substCodePlus [(x, v)] body
            Nothing -> return (m, CodeEpsilonElim (x, lowType) v branchList)
    _ -> return (m, CodeEpsilonElim (x, lowType) v branchList)
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
    ThetaUnaryOp op t@(LowTypeFloat _) (m1, DataFloat x _)
      | op == UnaryOpNeg -> upIntroData m (m1, DataFloat (-x) t)
    ThetaBinaryOp op t@(LowTypeSignedInt _) (m1, DataInt x _) (_, DataInt y _) -> do
      case op of
        BinaryOpAdd -> upIntroData m (m1, DataInt (x + y) t)
        BinaryOpSub -> upIntroData m (m1, DataInt (x - y) t)
        BinaryOpMul -> upIntroData m (m1, DataInt (x * y) t)
        BinaryOpDiv -> upIntroData m (m1, DataInt (x `div` y) t)
        BinaryOpRem -> upIntroData m (m1, DataInt (x `rem` y) t)
        BinaryOpEQ -> upIntroData m (m1, asData t $ x == y)
        BinaryOpNE -> upIntroData m (m1, asData t $ x /= y)
        BinaryOpGT -> upIntroData m (m1, asData t $ x > y)
        BinaryOpGE -> upIntroData m (m1, asData t $ x >= y)
        BinaryOpLT -> upIntroData m (m1, asData t $ x < y)
        BinaryOpLE -> upIntroData m (m1, asData t $ x <= y)
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
        BinaryOpEQ -> upIntroData m (m1, asData t $ x' == y')
        BinaryOpNE -> upIntroData m (m1, asData t $ x' /= y')
        BinaryOpGT -> upIntroData m (m1, asData t $ x' > y')
        BinaryOpGE -> upIntroData m (m1, asData t $ x' >= y')
        BinaryOpLT -> upIntroData m (m1, asData t $ x' < y')
        BinaryOpLE -> upIntroData m (m1, asData t $ x' <= y')
        BinaryOpShl -> upIntroData m (m1, DataInt (shiftL x y) t)
        BinaryOpLshr -> upIntroData m (m1, DataInt (ushiftR x y) t)
        BinaryOpAshr -> upIntroData m (m1, DataInt (shiftR x y) t)
        BinaryOpAnd -> upIntroData m (m1, DataInt (x .&. y) t)
        BinaryOpOr -> upIntroData m (m1, DataInt (x .|. y) t)
        BinaryOpXor -> upIntroData m (m1, DataInt (x `xor` y) t)
    ThetaBinaryOp op t@(LowTypeFloat _) (m1, DataFloat x _) (_, DataFloat y _) -> do
      case op of
        BinaryOpAdd -> upIntroData m (m1, DataFloat (x + y) t)
        BinaryOpSub -> upIntroData m (m1, DataFloat (x - y) t)
        BinaryOpMul -> upIntroData m (m1, DataFloat (x * y) t)
        BinaryOpDiv -> upIntroData m (m1, DataFloat (x / y) t)
        BinaryOpRem -> upIntroData m (m1, DataFloat (x `mod'` y) t)
        BinaryOpEQ -> upIntroData m (m1, asData t $ x == y)
        BinaryOpNE -> upIntroData m (m1, asData t $ x /= y)
        BinaryOpGT -> upIntroData m (m1, asData t $ x > y)
        BinaryOpGE -> upIntroData m (m1, asData t $ x >= y)
        BinaryOpLT -> upIntroData m (m1, asData t $ x < y)
        BinaryOpLE -> upIntroData m (m1, asData t $ x <= y)
        _ -> return (m, CodeTheta theta)
    ThetaPrint (_, DataInt i _) -> do
      liftIO $ putStr $ show i
      return (m, CodeUpIntro (Nothing, DataSigmaIntro []))
    _ -> return (m, CodeTheta theta)
reduceCodePlus t = return t

asData :: LowType -> Bool -> Data
asData t True = DataInt 1 t
asData t False = DataInt 0 t

upIntroData :: Monad m => a -> DataPlus -> m (a, Code)
upIntroData m d = return (m, CodeUpIntro d)
