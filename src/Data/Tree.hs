module Data.Tree where

import Data.Basic
import qualified Data.Set as S
import qualified Data.Text as T

data Tree
  = TreeLeaf T.Text
  | TreeNode [TreePlus]
  deriving (Show)

type TreePlus =
  (Meta, Tree)

asLeaf :: TreePlus -> Maybe (Meta, T.Text)
asLeaf tree =
  case tree of
    (m, TreeLeaf x) ->
      Just (m, x)
    _ ->
      Nothing

atomListOf :: TreePlus -> S.Set T.Text
atomListOf tree =
  case tree of
    (_, TreeLeaf x) ->
      S.singleton x
    (_, TreeNode ts) ->
      S.unions $ map atomListOf ts

showAsSExp :: TreePlus -> T.Text
showAsSExp tree =
  case tree of
    (_, TreeLeaf x) ->
      x
    (_, TreeNode ts) ->
      "(" <> T.intercalate " " (map showAsSExp ts) <> ")"

replaceMeta :: Meta -> TreePlus -> TreePlus
replaceMeta m tree =
  case tree of
    (m', TreeLeaf x) ->
      (supMeta m m', TreeLeaf x)
    (mt, TreeNode ts) -> do
      let ts' = map (replaceMeta m) ts
      (supMeta m mt, TreeNode ts')

substTree :: (T.Text, T.Text) -> TreePlus -> TreePlus
substTree sub@(from, to) tree =
  case tree of
    (m, TreeLeaf x)
      | x == from ->
        (m, TreeLeaf to)
      | otherwise ->
        (m, TreeLeaf x)
    (m, TreeNode ts) ->
      (m, TreeNode $ map (substTree sub) ts)
