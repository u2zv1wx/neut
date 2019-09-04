module Reduce.Code
  ( reduceCodePlus
  , inlineCodePlus
  ) where

import           Control.Monad.State

import           Data.Basic
import           Data.Code
import           Data.Env

reduceCodePlus :: CodePlus -> WithEnv CodePlus
reduceCodePlus (m, CodeTheta theta) =
  case theta of
    ThetaArith ArithAdd t (m1, DataEpsilonIntro (LiteralInteger i1) _) (_, DataEpsilonIntro (LiteralInteger i2) _) ->
      return
        (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 + i2) t))
    ThetaArith ArithSub t (m1, DataEpsilonIntro (LiteralInteger i1) _) (_, DataEpsilonIntro (LiteralInteger i2) _) ->
      return
        (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 - i2) t))
    ThetaArith ArithMul t (m1, DataEpsilonIntro (LiteralInteger i1) _) (_, DataEpsilonIntro (LiteralInteger i2) _) ->
      return
        (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 * i2) t))
    ThetaArith ArithDiv t (m1, DataEpsilonIntro (LiteralInteger i1) _) (_, DataEpsilonIntro (LiteralInteger i2) _) ->
      return
        (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 `div` i2) t))
    ThetaPrint (_, DataEpsilonIntro (LiteralInteger i) _) -> do
      liftIO $ putStr $ show i
      return (m, CodeUpIntro (Nothing, DataSigmaIntro []))
    _ -> return (m, CodeTheta theta)
reduceCodePlus (m, CodeEpsilonElim x v branchList) =
  case v of
    (_, DataEpsilonIntro l _) ->
      case lookup (CaseLiteral l) branchList of
        Just body -> reduceCodePlus $ substCodePlus [(x, v)] body
        Nothing ->
          case lookup CaseDefault branchList of
            Just body -> reduceCodePlus $ substCodePlus [(x, v)] body
            Nothing   -> return (m, CodeEpsilonElim x v branchList)
    _ -> return (m, CodeEpsilonElim x v branchList)
reduceCodePlus (m, CodePiElimDownElim (m2, DataDownIntroPiIntro xs body) es) = do
  es' <- mapM reduceCodePlus es
  case extractUpIntro es' of
    Just vs -> reduceCodePlus $ substCodePlus (zip xs vs) body
    Nothing ->
      return (m, CodePiElimDownElim (m2, DataDownIntroPiIntro xs body) es')
reduceCodePlus (m, CodePiElimDownElim v@(_, DataTheta x) es) = do
  es' <- mapM reduceCodePlus es
  cenv <- gets codeEnv
  case lookup x cenv of
    Just (xs, body)
      | Just vs <- extractUpIntro es' ->
        reduceCodePlus $ substCodePlus (zip xs vs) body
    _ -> return (m, CodePiElimDownElim v es')
reduceCodePlus (m, CodeSigmaElim xs v e) =
  case v of
    (_, DataSigmaIntro es)
      | length es == length xs -> reduceCodePlus $ substCodePlus (zip xs es) e
    _ -> return (m, CodeSigmaElim xs v e)
reduceCodePlus t = return t

extractUpIntro :: [CodePlus] -> Maybe [DataPlus]
extractUpIntro [] = Just []
extractUpIntro ((_, CodeUpIntro v):es) = do
  vs <- extractUpIntro es
  return $ v : vs
extractUpIntro _ = Nothing

inlineCodePlus :: CodePlus -> WithEnv CodePlus
inlineCodePlus (m, CodeTheta theta) =
  case theta of
    ThetaArith ArithAdd t (m1, DataEpsilonIntro (LiteralInteger i1) _) (_, DataEpsilonIntro (LiteralInteger i2) _) ->
      return
        (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 + i2) t))
    ThetaArith ArithSub t (m1, DataEpsilonIntro (LiteralInteger i1) _) (_, DataEpsilonIntro (LiteralInteger i2) _) ->
      return
        (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 - i2) t))
    ThetaArith ArithMul t (m1, DataEpsilonIntro (LiteralInteger i1) _) (_, DataEpsilonIntro (LiteralInteger i2) _) ->
      return
        (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 * i2) t))
    ThetaArith ArithDiv t (m1, DataEpsilonIntro (LiteralInteger i1) _) (_, DataEpsilonIntro (LiteralInteger i2) _) ->
      return
        (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 `div` i2) t))
    ThetaPrint (_, DataEpsilonIntro (LiteralInteger i) _) -> do
      liftIO $ putStr $ show i
      return (m, CodeUpIntro (Nothing, DataSigmaIntro []))
    _ -> return (m, CodeTheta theta)
inlineCodePlus (m, CodeEpsilonElim x v branchList) =
  case v of
    (_, DataEpsilonIntro l _) ->
      case lookup (CaseLiteral l) branchList of
        Just body -> inlineCodePlus $ substCodePlus [(x, v)] body
        Nothing ->
          case lookup CaseDefault branchList of
            Just body -> inlineCodePlus $ substCodePlus [(x, v)] body
            Nothing -> do
              let (cs, es) = unzip branchList
              es' <- mapM inlineCodePlus es
              return (m, CodeEpsilonElim x v (zip cs es'))
    _ -> return (m, CodeEpsilonElim x v branchList)
inlineCodePlus (m1, CodePiElimDownElim (m2, DataDownIntroPiIntro xs body) es) = do
  es' <- mapM inlineCodePlus es
  case extractUpIntro es' of
    Nothing ->
      return (m1, CodePiElimDownElim (m2, DataDownIntroPiIntro xs body) es')
    Just vs -> inlineCodePlus $ substCodePlus (zip xs vs) body
inlineCodePlus (m, CodeSigmaElim xs v e) =
  case v of
    (_, DataSigmaIntro es)
      | length es == length xs -> inlineCodePlus $ substCodePlus (zip xs es) e
    _ -> do
      e' <- inlineCodePlus e
      return (m, CodeSigmaElim xs v e')
inlineCodePlus t = return t
