module Data.UnionFind
  ( UnionFind
  , run
  , union
  , find
  ) where

import Control.Monad.State

import qualified Data.IntMap.Strict as IntMap

type UnionFind a = State (IntMap.IntMap Int) a

run :: UnionFind a -> a
run comp = evalState comp IntMap.empty

union :: Int -> Int -> UnionFind ()
union x y = do
  x' <- find x
  y' <- find y
  modify (\tree -> IntMap.insert x' y' tree)

find :: Int -> UnionFind Int
find dom = do
  tree <- get
  case IntMap.lookup dom tree of
    Nothing -> return dom
    Just cod
      | cod == dom -> return cod
      | otherwise -> do
        cod' <- find cod
        put $ IntMap.insert dom cod' tree
        return cod'
