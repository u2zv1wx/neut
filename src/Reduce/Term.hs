module Reduce.Term
  ( reduceTerm
  ) where

import           Control.Monad.State
import           Control.Monad.Trans        (lift)
import           Control.Monad.Trans.Except

import           Data.Basic
import           Data.Env
import           Data.Term

reduceTerm :: Term -> WithEnv Term
reduceTerm (TermEpsilonElim x e branchList) = do
  e' <- reduceTerm e
  case e' of
    TermEpsilonIntro l _ ->
      case lookup (CaseLiteral l) branchList of
        Just body -> reduceTerm $ substTerm [(x, e')] body
        Nothing ->
          case lookup CaseDefault branchList of
            Just body -> reduceTerm $ substTerm [(x, e')] body
            Nothing ->
              lift $
              throwE $
              "the index " ++ show x ++ " is not included in branchList"
    _ -> return $ TermEpsilonElim x e' branchList
reduceTerm (TermPiElim e es) = do
  es' <- mapM reduceTerm es
  e' <- reduceTerm e
  case e' of
    TermPiIntro xs body
      | length xs == length es -> do
        let sub = zip xs es
        reduceTerm $ substTerm sub body
    TermConst constant
      | [TermEpsilonIntro (LiteralInteger x) sx, TermEpsilonIntro (LiteralInteger y) _] <-
         es' -> do
        let b1 = constant `elem` intAddConstantList
        let b2 = constant `elem` intSubConstantList
        let b3 = constant `elem` intMulConstantList
        let b4 = constant `elem` intDivConstantList
        case (b1, b2, b3, b4) of
          (True, _, _, _) ->
            return $ TermEpsilonIntro (LiteralInteger (x + y)) sx
          (_, True, _, _) ->
            return $ TermEpsilonIntro (LiteralInteger (x - y)) sx
          (_, _, True, _) ->
            return $ TermEpsilonIntro (LiteralInteger (x * y)) sx
          (_, _, _, True) ->
            return $ TermEpsilonIntro (LiteralInteger (x `div` y)) sx
          _ -> return $ TermPiElim e' es'
    _ -> return $ TermPiElim e' es'
reduceTerm (TermConstElim x es) = do
  es' <- mapM reduceTerm es
  env <- gets termEnv
  case lookup x env of
    Just (args, body)
      | length args == length es -> reduceTerm $ substTerm (zip args es') body
    _ -> return $ TermConstElim x es'
reduceTerm (TermSigmaElim xs e body) = do
  e' <- reduceTerm e
  case e' of
    TermSigmaIntro es -> reduceTerm $ substTerm (zip xs es) body
    _                 -> return $ TermSigmaElim xs e' body
reduceTerm (TermTauElim (TermTauIntro e)) = reduceTerm e
reduceTerm t = return t
