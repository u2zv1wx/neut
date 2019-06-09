module Reduce.WeakTerm
  ( reduceWeakTerm
  ) where

import           Control.Comonad.Cofree
import           Control.Monad.Trans        (lift)
import           Control.Monad.Trans.Except

import           Data.Basic
import           Data.Env
import           Data.WeakTerm

reduceWeakTerm :: WeakTerm -> WithEnv WeakTerm
reduceWeakTerm app@(i :< WeakTermPiElim _ _) = do
  let (fun, args) = toWeakTermPiElimSeq app
  args' <- mapM (sndM reduceWeakTerm) args
  fun' <- reduceWeakTerm fun
  case fun' of
    _ :< WeakTermPiIntro (x, _) e ->
      reduceWeakTerm $
      fromWeakTermPiElimSeq (substWeakTerm [(x, snd $ head args')] e, tail args')
    _ :< WeakTermConst constant -> do
      let b1 = constant `elem` intAddConstantList
      let b2 = constant `elem` intSubConstantList
      let b3 = constant `elem` intMulConstantList
      let b4 = constant `elem` intDivConstantList
      case (b1, b2, b3, b4, takeIntegerList (map snd args')) of
        (True, _, _, _, Just [x, y]) ->
          return $ i :< WeakTermIndexIntro (IndexInteger (x + y))
        (_, True, _, _, Just [x, y]) ->
          return $ i :< WeakTermIndexIntro (IndexInteger (x - y))
        (_, _, True, _, Just [x, y]) ->
          return $ i :< WeakTermIndexIntro (IndexInteger (x * y))
        (_, _, _, True, Just [x, y]) ->
          return $ i :< WeakTermIndexIntro (IndexInteger (x `div` y))
        _ -> return $ fromWeakTermPiElimSeq (fun', args')
    _ -> return $ fromWeakTermPiElimSeq (fun', args')
reduceWeakTerm (i :< WeakTermSigmaElim xs e body) = do
  e' <- reduceWeakTerm e
  case e of
    _ :< WeakTermSigmaIntro es -> do
      let _ :< body' = substWeakTerm (zip xs es) body
      reduceWeakTerm $ i :< body'
    _ -> return $ i :< WeakTermSigmaElim xs e' body
reduceWeakTerm (i :< WeakTermIndexElim e branchList) = do
  e' <- reduceWeakTerm e
  case e' of
    _ :< WeakTermIndexIntro x ->
      case lookup x branchList of
        Just body -> reduceWeakTerm body
        Nothing ->
          case lookup IndexDefault branchList of
            Just body -> reduceWeakTerm body
            Nothing ->
              lift $
              throwE $
              "the index " ++ show x ++ " is not included in branchList"
    _ -> return $ i :< WeakTermIndexElim e' branchList
reduceWeakTerm (meta :< WeakTermMu s e) =
  reduceWeakTerm $ substWeakTerm [(s, meta :< WeakTermMu s e)] e
reduceWeakTerm t = return t

takeIntegerList :: [WeakTerm] -> Maybe [Int]
takeIntegerList [] = Just []
takeIntegerList ((_ :< WeakTermIndexIntro (IndexInteger i)):rest) = do
  is <- takeIntegerList rest
  return (i : is)
takeIntegerList _ = Nothing

sndM :: Monad m => (a -> m b) -> (c, a) -> m (c, b)
sndM f (x, y) = do
  y' <- f y
  return (x, y')
