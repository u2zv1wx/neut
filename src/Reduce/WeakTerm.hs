module Reduce.WeakTerm
  ( reduceWeakTerm
  ) where

import           Control.Comonad.Cofree

import           Data.Basic
import           Data.WeakTerm

reduceWeakTerm :: WeakTerm -> WeakTerm
reduceWeakTerm app@(i :< WeakTermPiElim _ _) = do
  let (fun, args) = toWeakTermPiElimSeq app
  let args' = map (\(x, e) -> (x, reduceWeakTerm e)) args
  let fun' = reduceWeakTerm fun
  case fun' of
    _ :< WeakTermPiIntro (x, _) e ->
      reduceWeakTerm $
      fromWeakTermPiElimSeq
        (substWeakTerm [(x, snd $ head args')] e, tail args')
    _ :< WeakTermConst constant -> do
      let b1 = constant `elem` intAddConstantList
      let b2 = constant `elem` intSubConstantList
      let b3 = constant `elem` intMulConstantList
      let b4 = constant `elem` intDivConstantList
      case (b1, b2, b3, b4, takeIntegerList (map snd args')) of
        (True, _, _, _, Just [x, y]) ->
          i :< WeakTermIndexIntro (IndexInteger (x + y))
        (_, True, _, _, Just [x, y]) ->
          i :< WeakTermIndexIntro (IndexInteger (x - y))
        (_, _, True, _, Just [x, y]) ->
          i :< WeakTermIndexIntro (IndexInteger (x * y))
        (_, _, _, True, Just [x, y]) ->
          i :< WeakTermIndexIntro (IndexInteger (x `div` y))
        _ -> fromWeakTermPiElimSeq (fun', args')
    _ -> fromWeakTermPiElimSeq (fun', args')
reduceWeakTerm (i :< WeakTermSigmaElim xs e body) = do
  let e' = reduceWeakTerm e
  case e of
    _ :< WeakTermSigmaIntro es -> do
      let _ :< body' = substWeakTerm (zip xs es) body
      reduceWeakTerm $ i :< body'
    _ -> i :< WeakTermSigmaElim xs e' body
reduceWeakTerm (i :< WeakTermIndexElim e branchList) = do
  let e' = reduceWeakTerm e
  case e' of
    _ :< WeakTermIndexIntro x ->
      case lookup x branchList of
        Just body -> reduceWeakTerm body
        Nothing ->
          case lookup IndexDefault branchList of
            Just body -> reduceWeakTerm body
            Nothing   -> i :< WeakTermIndexElim e' branchList
    _ -> i :< WeakTermIndexElim e' branchList
reduceWeakTerm (meta :< WeakTermFix s e) =
  reduceWeakTerm $ substWeakTerm [(s, meta :< WeakTermFix s e)] e
reduceWeakTerm t = t

takeIntegerList :: [WeakTerm] -> Maybe [Int]
takeIntegerList [] = Just []
takeIntegerList ((_ :< WeakTermIndexIntro (IndexInteger i)):rest) = do
  is <- takeIntegerList rest
  return (i : is)
takeIntegerList _ = Nothing
