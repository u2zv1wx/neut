module Reduce.Code
  ( reduceCodePlus
  ) where

import           Control.Monad.Trans

import           Data.Basic
import           Data.Code
import           Data.Env

reduceCodePlus :: CodePlus -> WithEnv CodePlus
reduceCodePlus (m, CodeTheta theta) =
  case theta of
    ThetaArith ArithAdd (m1, DataEpsilonIntro (LiteralInteger i1)) (_, DataEpsilonIntro (LiteralInteger i2)) ->
      return (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 + i2)))
    ThetaArith ArithSub (m1, DataEpsilonIntro (LiteralInteger i1)) (_, DataEpsilonIntro (LiteralInteger i2)) ->
      return (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 - i2)))
    ThetaArith ArithMul (m1, DataEpsilonIntro (LiteralInteger i1)) (_, DataEpsilonIntro (LiteralInteger i2)) ->
      return (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 * i2)))
    ThetaArith ArithDiv (m1, DataEpsilonIntro (LiteralInteger i1)) (_, DataEpsilonIntro (LiteralInteger i2)) ->
      return
        (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 `div` i2)))
    ThetaPrint (_, DataEpsilonIntro (LiteralInteger i)) -> do
      liftIO $ putStr $ show i
      let topType = (DataMetaTerminal Nothing, DataEpsilon "top")
      let topMeta = DataMetaNonTerminal topType Nothing
      return (m, CodeUpIntro (topMeta, DataEpsilonIntro (LiteralLabel "unit")))
    _ -> return (m, CodeTheta theta)
reduceCodePlus (m, CodeEpsilonElim (x, t) v branchList) =
  case v of
    (_, DataEpsilonIntro l) ->
      case lookup (CaseLiteral l) branchList of
        Just body -> reduceCodePlus $ substCodePlus [(x, v)] body
        Nothing ->
          case lookup CaseDefault branchList of
            Just body -> reduceCodePlus $ substCodePlus [(x, v)] body
            Nothing   -> return (m, CodeEpsilonElim (x, t) v branchList)
    _ -> return (m, CodeEpsilonElim (x, t) v branchList)
reduceCodePlus (m, CodePiElimDownElim v vs)
  -- e' <- reduceCodePlus e
 = do
  case v of
    (_, DataDownIntroPiIntro xts body)
      | length xts == length vs -> do
        let xs = map fst xts
        reduceCodePlus $ substCodePlus (zip xs vs) body
    _ -> return (m, CodePiElimDownElim v vs)
reduceCodePlus (m, CodeSigmaElim xts v e) =
  case v of
    (_, DataSigmaIntro es)
      | length es == length xts -> do
        let xs = map fst xts
        reduceCodePlus $ substCodePlus (zip xs es) e
    _ -> return (m, CodeSigmaElim xts v e)
reduceCodePlus (m, CodeUpElim (x, t) e1 e2) = do
  e1' <- reduceCodePlus e1
  case e1' of
    (_, CodeUpIntro v) -> reduceCodePlus $ substCodePlus [(x, v)] e2
    _                  -> return (m, CodeUpElim (x, t) e1' e2)
-- reduceCodePlus self@(m', CodeMu (x, t) body) = do
--   let meta = DataMetaNonTerminal t (obtainLocation m')
--   let x' = (meta, DataDownIntro self)
--   reduceCodePlus $ substCodePlus [(x, x')] body
reduceCodePlus t = return t

obtainLocation :: CodeMeta -> Maybe (Int, Int)
obtainLocation (CodeMetaTerminal ml)      = ml
obtainLocation (CodeMetaNonTerminal _ ml) = ml
