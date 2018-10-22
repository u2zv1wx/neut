module Exhaust where

import Control.Monad.State
import Control.Monad.Trans.Except

import Control.Comonad.Cofree

import Data
import Data.List
import Reduce

import qualified Text.Show.Pretty as Pr

exhaust :: Neut -> WithEnv Neut
exhaust e = do
  b <- exhaust' e
  if b
    then return e
    else lift $ throwE "non-exhaustive pattern"

exhaust' :: Neut -> WithEnv Bool
exhaust' (_ :< NeutVar _) = return True
exhaust' (_ :< NeutPi (_, tdom) tcod) = do
  b1 <- exhaust' tdom
  b2 <- exhaust' tcod
  return $ b1 && b2
exhaust' (_ :< NeutPiIntro _ e) = exhaust' e
exhaust' (_ :< NeutPiElim e1 e2) = do
  b1 <- exhaust' e1
  b2 <- exhaust' e2
  return $ b1 && b2
exhaust' (_ :< NeutSigma xts t2) = do
  let (_, ts) = unzip xts
  bs <- mapM exhaust' ts
  b2 <- exhaust' t2
  return $ and bs && b2
exhaust' (_ :< NeutSigmaIntro es) = do
  bs <- mapM exhaust' es
  return $ and bs
exhaust' (_ :< NeutSigmaElim e1 _ e2) = do
  b1 <- exhaust' e1
  b2 <- exhaust' e2
  return $ b1 && b2
exhaust' (_ :< NeutBox e) = exhaust' e
exhaust' (_ :< NeutBoxIntro e) = exhaust' e
exhaust' (_ :< NeutBoxElim e) = exhaust' e
exhaust' (_ :< NeutMu _ e) = exhaust' e
exhaust' (_ :< NeutIndex _) = return True
exhaust' (_ :< NeutIndexIntro _) = return True
exhaust' (_ :< NeutIndexElim _ []) = return False -- empty clause?
exhaust' (meta :< NeutIndexElim e1 branchList@((l, _):_)) = do
  b1 <- exhaust' e1
  t <- lookupTypeEnv' meta >>= reduce
  let labelList = map fst branchList
  case t of
    _ :< NeutIndex "i32" ->
      return $ b1 && (IndexDefault `elem` labelList || hasVar labelList)
    _ ->
      if IndexDefault `elem` labelList
        then return b1
        else case l of
               IndexLabel x -> do
                 set <- lookupIndexSet x
                 if length set <= length (nub labelList)
                   then return True
                   else return False
               _ -> return False
exhaust' (_ :< NeutConst t) = exhaust' t
exhaust' (_ :< NeutConstIntro _) = return True
exhaust' (_ :< NeutConstElim e) = exhaust' e
exhaust' (_ :< NeutUniv _) = return True
exhaust' (_ :< NeutHole _) = return False

hasVar :: [Index] -> Bool
hasVar [] = False
hasVar (IndexLabel _:_) = True
hasVar (_:is) = hasVar is
