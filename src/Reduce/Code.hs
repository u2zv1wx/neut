module Reduce.Code
  ( reduceCodePlus
  ) where

import Control.Monad.State
import Unsafe.Coerce -- for int -> word, word -> int

import Data.Basic
import Data.Code
import Data.Env

reduceCodePlus :: CodePlus -> WithEnv CodePlus
reduceCodePlus (m, CodeTheta theta) =
  case theta of
    ThetaBinOp BinOpAdd t@(LowTypeSignedInt _) (m1, DataInt i1 _) (_, DataInt i2 _) ->
      return (m, CodeUpIntro (m1, DataInt (i1 + i2) t))
    ThetaBinOp BinOpSub t@(LowTypeSignedInt _) (m1, DataInt i1 _) (_, DataInt i2 _) ->
      return (m, CodeUpIntro (m1, DataInt (i1 - i2) t))
    ThetaBinOp BinOpMul t@(LowTypeSignedInt _) (m1, DataInt i1 _) (_, DataInt i2 _) ->
      return (m, CodeUpIntro (m1, DataInt (i1 * i2) t))
    ThetaBinOp BinOpDiv t@(LowTypeSignedInt _) (m1, DataInt i1 _) (_, DataInt i2 _) ->
      return (m, CodeUpIntro (m1, DataInt (i1 `div` i2) t))
    ThetaBinOp BinOpAdd t@(LowTypeUnsignedInt _) (m1, DataInt i1 _) (_, DataInt i2 _) ->
      return (m, CodeUpIntro (m1, DataInt (i1 + i2) t))
    ThetaBinOp BinOpSub t@(LowTypeUnsignedInt _) (m1, DataInt i1 _) (_, DataInt i2 _) ->
      return (m, CodeUpIntro (m1, DataInt (i1 - i2) t))
    ThetaBinOp BinOpMul t@(LowTypeUnsignedInt _) (m1, DataInt i1 _) (_, DataInt i2 _) ->
      return (m, CodeUpIntro (m1, DataInt (i1 * i2) t))
    ThetaBinOp BinOpDiv t@(LowTypeUnsignedInt _) (m1, DataInt i1 _) (_, DataInt i2 _) -> do
      let i1' = unsafeCoerce i1 :: Word
      let i2' = unsafeCoerce i2 :: Word
      let i = i1' `div` i2'
      return (m, CodeUpIntro (m1, DataInt (unsafeCoerce i) t))
    ThetaBinOp BinOpAdd t@(LowTypeFloat _) (m1, DataFloat i1 _) (_, DataFloat i2 _) ->
      return (m, CodeUpIntro (m1, DataFloat (i1 + i2) t))
    ThetaBinOp BinOpSub t@(LowTypeFloat _) (m1, DataFloat i1 _) (_, DataFloat i2 _) ->
      return (m, CodeUpIntro (m1, DataFloat (i1 - i2) t))
    ThetaBinOp BinOpMul t@(LowTypeFloat _) (m1, DataFloat i1 _) (_, DataFloat i2 _) ->
      return (m, CodeUpIntro (m1, DataFloat (i1 * i2) t))
    ThetaBinOp BinOpDiv t@(LowTypeFloat _) (m1, DataFloat i1 _) (_, DataFloat i2 _) ->
      return (m, CodeUpIntro (m1, DataFloat (i1 / i2) t))
    ThetaPrint (_, DataInt i _) -> do
      liftIO $ putStr $ show i
      return (m, CodeUpIntro (Nothing, DataSigmaIntro []))
    _ -> return (m, CodeTheta theta)
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
reduceCodePlus t = return t
