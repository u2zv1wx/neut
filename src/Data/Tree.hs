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
replaceMeta m (_, TreeLeaf x) = (m, TreeLeaf x)
replaceMeta m (_, TreeNode ts) = do
  let ts' = map (replaceMeta m) ts
  (m, TreeNode ts')
replaceMeta m (_, TreeNodeSquare ts) = do
  let ts' = map (replaceMeta m) ts
  (m, TreeNodeSquare ts')
