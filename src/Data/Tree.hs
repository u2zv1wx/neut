module Data.Tree where

import Data.Meta
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

headAtomOf :: TreePlus -> Maybe T.Text
headAtomOf tree =
  case tree of
    (_, TreeLeaf x) ->
      return x
    (_, TreeNode ((_, TreeLeaf x) : _)) ->
      return x
    (_, TreeNode _) ->
      Nothing

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
