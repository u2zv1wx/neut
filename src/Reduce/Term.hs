module Reduce.Term
  ( reduceTerm
  ) where

import           Control.Monad              (forM)
import           Control.Monad.Trans        (lift)
import           Control.Monad.Trans.Except
import           Data.Basic
import           Data.Env
import           Data.Term

reduceTerm :: Term -> WithEnv Term
reduceTerm app@(TermPiElim _ _) = do
  let (fun, args) = toTermPiElimSeq app
  fun' <- reduceTerm fun
  case fun' of
    TermPiIntro x body ->
      reduceTerm $
      fromTermPiElimSeq (substTerm [(x, head args)] body, tail args)
    TermConst constant -> do
      args' <- mapM reduceTerm args
      let b1 = constant `elem` intAddConstantList
      let b2 = constant `elem` intSubConstantList
      let b3 = constant `elem` intMulConstantList
      let b4 = constant `elem` intDivConstantList
      let t = LowTypeSignedInt 64 -- for now
      case (b1, b2, b3, b4, takeIntegerList args') of
        (True, _, _, _, Just [x, y]) ->
          return $ TermIndexIntro (IndexInteger (x + y)) t
        (_, True, _, _, Just [x, y]) ->
          return $ TermIndexIntro (IndexInteger (x - y)) t
        (_, _, True, _, Just [x, y]) ->
          return $ TermIndexIntro (IndexInteger (x * y)) t
        (_, _, _, True, Just [x, y]) ->
          return $ TermIndexIntro (IndexInteger (x `div` y)) t
        _ -> return $ fromTermPiElimSeq (fun', args')
    _ -> return $ fromTermPiElimSeq (fun', args)
reduceTerm (TermSigmaElim e xs body) = do
  e' <- reduceTerm e
  case e' of
    TermSigmaIntro es -> reduceTerm $ substTerm (zip xs es) body
    _                 -> return $ TermSigmaElim e' xs body
reduceTerm (TermIndexElim e branchList) = do
  e' <- reduceTerm e
  case e' of
    TermIndexIntro x _ ->
      case lookup x branchList of
        Just body -> reduceTerm body
        Nothing ->
          case lookup IndexDefault branchList of
            Just body -> reduceTerm body
            Nothing ->
              lift $
              throwE $
              "the index " ++ show x ++ " is not included in branchList"
    _ -> return $ TermIndexElim e' branchList
reduceTerm t = return t

takeIntegerList :: [Term] -> Maybe [Int]
takeIntegerList [] = Just []
takeIntegerList (TermIndexIntro (IndexInteger i) _:rest) = do
  is <- takeIntegerList rest
  return (i : is)
takeIntegerList _ = Nothing
