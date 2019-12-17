module Reduce.Code
  ( reduceCodePlus
  ) where

import Control.Monad.State
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
    ThetaBinaryOp op t@(LowTypeSignedInt _) (m1, DataInt i1 _) (_, DataInt i2 _)
      | op `elem` arithOpList -> do
        case op of
          BinaryOpAdd -> return (m, CodeUpIntro (m1, DataInt (i1 + i2) t))
          BinaryOpSub -> return (m, CodeUpIntro (m1, DataInt (i1 - i2) t))
          BinaryOpMul -> return (m, CodeUpIntro (m1, DataInt (i1 * i2) t))
          BinaryOpDiv -> return (m, CodeUpIntro (m1, DataInt (i1 `div` i2) t))
          _ -> return (m, CodeTheta theta)
    ThetaBinaryOp op t@(LowTypeUnsignedInt _) (m1, DataInt i1 _) (_, DataInt i2 _)
      | op `elem` arithOpList -> do
        case op of
          BinaryOpAdd -> return (m, CodeUpIntro (m1, DataInt (i1 + i2) t))
          BinaryOpSub -> return (m, CodeUpIntro (m1, DataInt (i1 - i2) t))
          BinaryOpMul -> return (m, CodeUpIntro (m1, DataInt (i1 * i2) t))
          BinaryOpDiv -> do
            let i1' = unsafeCoerce i1 :: Word
            let i2' = unsafeCoerce i2 :: Word
            let i = i1' `div` i2'
            return (m, CodeUpIntro (m1, DataInt (unsafeCoerce i) t))
          _ -> return (m, CodeTheta theta)
    ThetaBinaryOp op t@(LowTypeFloat _) (m1, DataFloat i1 _) (_, DataFloat i2 _)
      | op `elem` arithOpList -> do
        case op of
          BinaryOpAdd -> return (m, CodeUpIntro (m1, DataFloat (i1 + i2) t))
          BinaryOpSub -> return (m, CodeUpIntro (m1, DataFloat (i1 - i2) t))
          BinaryOpMul -> return (m, CodeUpIntro (m1, DataFloat (i1 * i2) t))
          BinaryOpDiv -> return (m, CodeUpIntro (m1, DataFloat (i1 / i2) t))
          _ -> return (m, CodeTheta theta)
    ThetaBinaryOp op t@(LowTypeSignedInt _) (m1, DataInt i1 _) (_, DataInt i2 _)
      | op `elem` compareOpList -> do
        case op of
          BinaryOpEQ -> return (m, CodeUpIntro (m1, asData t $ i1 == i2))
          BinaryOpNE -> return (m, CodeUpIntro (m1, asData t $ i1 /= i2))
          BinaryOpGT -> return (m, CodeUpIntro (m1, asData t $ i1 > i2))
          BinaryOpGE -> return (m, CodeUpIntro (m1, asData t $ i1 >= i2))
          BinaryOpLT -> return (m, CodeUpIntro (m1, asData t $ i1 < i2))
          BinaryOpLE -> return (m, CodeUpIntro (m1, asData t $ i1 <= i2))
          _ -> return (m, CodeTheta theta)
    ThetaBinaryOp op t@(LowTypeUnsignedInt _) (m1, DataInt i1 _) (_, DataInt i2 _)
      | op `elem` compareOpList -> do
        let i1' = unsafeCoerce i1 :: Word
        let i2' = unsafeCoerce i2 :: Word
        case op of
          BinaryOpEQ -> return (m, CodeUpIntro (m1, asData t $ i1' == i2'))
          BinaryOpNE -> return (m, CodeUpIntro (m1, asData t $ i1' /= i2'))
          BinaryOpGT -> return (m, CodeUpIntro (m1, asData t $ i1' > i2'))
          BinaryOpGE -> return (m, CodeUpIntro (m1, asData t $ i1' >= i2'))
          BinaryOpLT -> return (m, CodeUpIntro (m1, asData t $ i1' < i2'))
          BinaryOpLE -> return (m, CodeUpIntro (m1, asData t $ i1' <= i2'))
          _ -> return (m, CodeTheta theta)
    ThetaBinaryOp op t@(LowTypeFloat _) (m1, DataFloat i1 _) (_, DataFloat i2 _)
      | op `elem` compareOpList -> do
        case op of
          BinaryOpEQ -> return (m, CodeUpIntro (m1, asData t $ i1 == i2))
          BinaryOpNE -> return (m, CodeUpIntro (m1, asData t $ i1 /= i2))
          BinaryOpGT -> return (m, CodeUpIntro (m1, asData t $ i1 > i2))
          BinaryOpGE -> return (m, CodeUpIntro (m1, asData t $ i1 >= i2))
          BinaryOpLT -> return (m, CodeUpIntro (m1, asData t $ i1 < i2))
          BinaryOpLE -> return (m, CodeUpIntro (m1, asData t $ i1 <= i2))
          _ -> return (m, CodeTheta theta)
    ThetaPrint (_, DataInt i _) -> do
      liftIO $ putStr $ show i
      return (m, CodeUpIntro (Nothing, DataSigmaIntro []))
    _ -> return (m, CodeTheta theta)
reduceCodePlus t = return t

asData :: LowType -> Bool -> Data
asData t True = DataInt 1 t
asData t False = DataInt 0 t
