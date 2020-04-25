module Data.Basic where

import qualified Data.IntMap as IntMap
import qualified Data.Set as S
import qualified Data.Text as T

{-# INLINE nsSep #-}
nsSep :: T.Text
nsSep =
  "."

linearCheck :: (Eq a, Ord a) => [a] -> Bool
linearCheck =
  linearCheck' S.empty

linearCheck' :: (Eq a, Ord a) => S.Set a -> [a] -> Bool
linearCheck' found input =
  case input of
    [] ->
      True
    (x : xs)
      | x `S.member` found ->
        False
      | otherwise ->
        linearCheck' (S.insert x found) xs

deleteKeys :: IntMap.IntMap a -> [Int] -> IntMap.IntMap a
deleteKeys =
  foldr IntMap.delete

fmap2 :: (Functor f, Functor g) => (a -> b) -> f (g a) -> f (g b)
fmap2 f =
  fmap (fmap f)
