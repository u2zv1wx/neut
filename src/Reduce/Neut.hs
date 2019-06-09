module Reduce.Neut
  ( reduceNeut
  ) where

import           Control.Comonad.Cofree
import           Control.Monad.Trans        (lift)
import           Control.Monad.Trans.Except

import           Data.Basic
import           Data.Env
import           Data.Neut

reduceNeut :: Neut -> WithEnv Neut
reduceNeut app@(i :< NeutPiElim _ _) = do
  let (fun, args) = toNeutPiElimSeq app
  args' <- mapM (sndM reduceNeut) args
  fun' <- reduceNeut fun
  case fun' of
    _ :< NeutPiIntro (x, _) e ->
      reduceNeut $
      fromNeutPiElimSeq (substNeut [(x, snd $ head args')] e, tail args')
    _ :< NeutConst constant -> do
      let b1 = constant `elem` intAddConstantList
      let b2 = constant `elem` intSubConstantList
      let b3 = constant `elem` intMulConstantList
      let b4 = constant `elem` intDivConstantList
      case (b1, b2, b3, b4, takeIntegerList (map snd args')) of
        (True, _, _, _, Just [x, y]) ->
          return $ i :< NeutIndexIntro (IndexInteger (x + y))
        (_, True, _, _, Just [x, y]) ->
          return $ i :< NeutIndexIntro (IndexInteger (x - y))
        (_, _, True, _, Just [x, y]) ->
          return $ i :< NeutIndexIntro (IndexInteger (x * y))
        (_, _, _, True, Just [x, y]) ->
          return $ i :< NeutIndexIntro (IndexInteger (x `div` y))
        _ -> return $ fromNeutPiElimSeq (fun', args')
    _ -> return $ fromNeutPiElimSeq (fun', args')
reduceNeut (i :< NeutSigmaElim xs e body) = do
  e' <- reduceNeut e
  case e of
    _ :< NeutSigmaIntro es -> do
      let _ :< body' = substNeut (zip xs es) body
      reduceNeut $ i :< body'
    _ -> return $ i :< NeutSigmaElim xs e' body
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

sndM :: Monad m => (a -> m b) -> (c, a) -> m (c, b)
sndM f (x, y) = do
  y' <- f y
  return (x, y')
