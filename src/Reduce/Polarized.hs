module Reduce.Polarized
  ( reduceNeg
  ) where

import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Data.Basic
import           Data.Env
import           Data.Polarized

reduceNeg :: Neg -> WithEnv Neg
reduceNeg (NegPiElimDownElim v vs) =
  case v of
    PosConst x -> do
      penv <- gets polEnv
      case lookup x penv of
        Just (args, body)
          | length args == length vs -> reduceNeg $ substNeg (zip args vs) body
        _ -> return $ NegPiElimDownElim v vs
    _ -> return $ NegPiElimDownElim v vs
reduceNeg (NegSigmaElim xs v body) =
  case v of
    PosSigmaIntro vs
      | length xs == length vs -> reduceNeg $ substNeg (zip xs vs) body
    _ -> return $ NegSigmaElim xs v body
reduceNeg (NegEpsilonElim v branchList) =
  case v of
    PosEpsilonIntro l _ ->
      case lookup (CaseLiteral l) branchList of
        Just body -> reduceNeg body
        Nothing ->
          case lookup CaseDefault branchList of
            Just body -> reduceNeg body
            Nothing ->
              lift $
              throwE $
              "the index " ++ show l ++ " is not included in branchList"
    _ -> return $ NegEpsilonElim v branchList
reduceNeg (NegUpElim x e1 e2) = do
  e1' <- reduceNeg e1
  case e1' of
    NegUpIntro v -> reduceNeg $ substNeg [(x, v)] e2
    _            -> return $ NegUpElim x e1' e2
reduceNeg (NegConstElim (ConstantLabel x) vs) = do
  penv <- gets polEnv
  case lookup x penv of
    Just (args, body)
      | length args == length vs -> reduceNeg $ substNeg (zip args vs) body
    _ -> return $ NegConstElim (ConstantLabel x) vs
reduceNeg (NegConstElim c vs) = do
  let xs = takeIntegerList vs
  let t = LowTypeSignedInt 64 -- for now
  case (c, xs) of
    (ConstantArith _ ArithAdd, Just [x, y]) ->
      return $ NegUpIntro (PosEpsilonIntro (LiteralInteger (x + y)) t)
    (ConstantArith _ ArithSub, Just [x, y]) ->
      return $ NegUpIntro (PosEpsilonIntro (LiteralInteger (x - y)) t)
    (ConstantArith _ ArithMul, Just [x, y]) ->
      return $ NegUpIntro (PosEpsilonIntro (LiteralInteger (x * y)) t)
    (ConstantArith _ ArithDiv, Just [x, y]) ->
      return $ NegUpIntro (PosEpsilonIntro (LiteralInteger (x `div` y)) t)
    _ -> return $ NegConstElim c vs
reduceNeg e = return e

takeIntegerList :: [Pos] -> Maybe [Int]
takeIntegerList [] = Just []
takeIntegerList (PosEpsilonIntro (LiteralInteger i) _:rest) = do
  is <- takeIntegerList rest
  return (i : is)
takeIntegerList _ = Nothing
