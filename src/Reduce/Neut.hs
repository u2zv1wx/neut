module Reduce.Neut
  ( reduceNeut
  ) where

import           Control.Comonad.Cofree
import           Control.Monad              (forM)
import           Control.Monad.Trans        (lift)
import           Control.Monad.Trans.Except

import           Data.Basic
import           Data.Env
import           Data.Neut

reduceNeut :: Neut -> WithEnv Neut
reduceNeut app@(i :< NeutPiElim _ _) = do
  let (fun, args) = toNeutPiElimSeq app
  args' <-
    forM args $ \(x, e) -> do
      e' <- reduceNeut e
      return (x, e')
  fun' <- reduceNeut fun
  case fun' of
    lam@(_ :< NeutPiIntro _ _)
      | (body, xtms) <- toNeutPiIntroSeq lam
      , length xtms == length args -> do
        let xs = map (\(x, _, _) -> x) xtms
        let es = map snd args'
        reduceNeut $ substNeut (zip xs es) body
    _ ->
      case fun' of
        _ :< NeutConst constant
          | constant `elem` intAddConstantList
          , Just [x, y] <- takeIntegerList (map snd args') ->
            return $ i :< NeutIndexIntro (IndexInteger (x + y))
        _ :< NeutConst constant
          | constant `elem` intSubConstantList
          , Just [x, y] <- takeIntegerList (map snd args') ->
            return $ i :< NeutIndexIntro (IndexInteger (x - y))
        _ :< NeutConst constant
          | constant `elem` intMulConstantList
          , Just [x, y] <- takeIntegerList (map snd args') ->
            return $ i :< NeutIndexIntro (IndexInteger (x * y))
        _ :< NeutConst constant
          | constant `elem` intDivConstantList
          , Just [x, y] <- takeIntegerList (map snd args') ->
            return $ i :< NeutIndexIntro (IndexInteger (x `div` y))
        _ -> return $ fromNeutPiElimSeq (fun', args')
reduceNeut (i :< NeutSigmaElim e xs body) = do
  e' <- reduceNeut e
  case e of
    _ :< NeutSigmaIntro es -> do
      let _ :< body' = substNeut (zip xs es) body
      reduceNeut $ i :< body'
    _ -> return $ i :< NeutSigmaElim e' xs body
reduceNeut (i :< NeutIndexElim e branchList) = do
  e' <- reduceNeut e
  case e' of
    _ :< NeutIndexIntro x ->
      case lookup x branchList of
        Just body -> reduceNeut body
        Nothing ->
          case lookup IndexDefault branchList of
            Just body -> reduceNeut body
            Nothing ->
              lift $
              throwE $
              "the index " ++ show x ++ " is not included in branchList"
    _ -> return $ i :< NeutIndexElim e' branchList
reduceNeut (meta :< NeutMu s e) =
  reduceNeut $ substNeut [(s, meta :< NeutMu s e)] e
reduceNeut t = return t

takeIntegerList :: [Neut] -> Maybe [Int]
takeIntegerList [] = Just []
takeIntegerList ((_ :< NeutIndexIntro (IndexInteger i)):rest) = do
  is <- takeIntegerList rest
  return (i : is)
takeIntegerList _ = Nothing
