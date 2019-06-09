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
        Just (DeclarationFun args body)
          | length args == length vs -> reduceNeg $ substNeg (zip args vs) body
        Just (DeclarationConst v1') -> reduceNeg $ NegPiElimDownElim v1' vs
        _ -> return $ NegPiElimDownElim v vs
    _ -> return $ NegPiElimDownElim v vs
-- reduceNeg (NegPiElimDownElim v1 v2) =
--   case v1 of
--     PosConst x -> do
--       penv <- gets polEnv
--       case lookup x penv of
--         Just (DeclarationFun arg body) -> reduceNeg $ substNeg [(arg, v2)] body
--         Just (DeclarationConst v1') -> reduceNeg $ NegPiElimDownElim v1' v2
--         _ -> return $ NegPiElimDownElim v1 v2
--     _ -> return $ NegPiElimDownElim v1 v2
reduceNeg (NegSigmaElim v xs body) =
  case v of
    PosSigmaIntro vs
      | length xs == length vs -> reduceNeg $ substNeg (zip xs vs) body
    PosConst x -> do
      penv <- gets polEnv
      case lookup x penv of
        Just (DeclarationConst v') -> reduceNeg $ NegSigmaElim v' xs body
        _ -> do
          liftIO $ putStrLn $ "not found: " ++ show x
          return $ NegSigmaElim v xs body
    _ -> return $ NegSigmaElim v xs body
reduceNeg (NegIndexElim v branchList) =
  case v of
    PosIndexIntro x _ ->
      case lookup x branchList of
        Just body -> reduceNeg body
        Nothing ->
          case lookup IndexDefault branchList of
            Just body -> reduceNeg body
            Nothing ->
              lift $
              throwE $
              "the index " ++ show x ++ " is not included in branchList"
    _ -> return $ NegIndexElim v branchList
reduceNeg (NegUpElim x e1 e2) = do
  e1' <- reduceNeg e1
  case e1' of
    NegUpIntro v -> reduceNeg $ substNeg [(x, v)] e2
    _            -> return $ NegUpElim x e1' e2
reduceNeg (NegConstElim c vs) = do
  let xs = takeIntegerList vs
  let t = LowTypeSignedInt 64 -- for now
  case (c, xs) of
    (ConstantArith _ ArithAdd, Just [x, y]) ->
      return $ NegUpIntro (PosIndexIntro (IndexInteger (x + y)) t)
    (ConstantArith _ ArithSub, Just [x, y]) ->
      return $ NegUpIntro (PosIndexIntro (IndexInteger (x - y)) t)
    (ConstantArith _ ArithMul, Just [x, y]) ->
      return $ NegUpIntro (PosIndexIntro (IndexInteger (x * y)) t)
    (ConstantArith _ ArithDiv, Just [x, y]) ->
      return $ NegUpIntro (PosIndexIntro (IndexInteger (x `div` y)) t)
    _ -> return $ NegConstElim c vs
reduceNeg e = return e

takeIntegerList :: [Pos] -> Maybe [Int]
takeIntegerList [] = Just []
takeIntegerList (PosIndexIntro (IndexInteger i) _:rest) = do
  is <- takeIntegerList rest
  return (i : is)
takeIntegerList _ = Nothing
