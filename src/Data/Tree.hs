{-# LANGUAGE OverloadedStrings #-}

module Data.Tree where

import Data.Basic

import qualified Data.Set as S
import qualified Data.Text as T

data Tree
  = TreeLeaf T.Text
  | TreeNode [TreePlus]
  | TreeNodeSquare [TreePlus]
  deriving (Show)

type TreePlus = (Meta, Tree)

asLeaf :: TreePlus -> Maybe (Meta, T.Text)
asLeaf (m, TreeLeaf x) = Just (m, x)
asLeaf _ = Nothing

atomListOf :: TreePlus -> S.Set T.Text
atomListOf (_, TreeLeaf x) = S.singleton x
atomListOf (_, TreeNode ts) = S.unions $ map atomListOf ts
atomListOf (_, TreeNodeSquare ts) = S.unions $ map atomListOf ts

showAsSExp :: TreePlus -> T.Text
showAsSExp (_, TreeLeaf x) = x
showAsSExp (_, TreeNode ts) =
  "(" <> T.intercalate " " (map showAsSExp ts) <> ")"
showAsSExp (_, TreeNodeSquare ts) =
  "[" <> T.intercalate " " (map showAsSExp ts) <> "]"

replaceMeta :: Meta -> TreePlus -> TreePlus
replaceMeta m (m', TreeLeaf x) = (supMeta m m', TreeLeaf x)
replaceMeta m (mt, TreeNode ts) = do
  let ts' = map (replaceMeta m) ts
  (supMeta m mt, TreeNode ts')
replaceMeta m (mt, TreeNodeSquare ts) = do
  let ts' = map (replaceMeta m) ts
  (supMeta m mt, TreeNodeSquare ts')

substTree :: (T.Text, T.Text) -> TreePlus -> TreePlus
substTree (from, to) (m, TreeLeaf x)
  | x == from = (m, TreeLeaf to)
  | otherwise = (m, TreeLeaf x)
substTree sub (m, TreeNode ts) = (m, TreeNode $ map (substTree sub) ts)
substTree sub (m, TreeNodeSquare ts) = (m, TreeNode $ map (substTree sub) ts)
