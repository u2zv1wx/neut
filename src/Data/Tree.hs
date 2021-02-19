module Data.Tree where

import Data.Hint
import qualified Data.Text as T

data Tree
  = TreeLeaf T.Text
  | TreeNode [TreePlus]
  deriving (Show)

type TreePlus =
  (Hint, Tree)

asLeaf :: TreePlus -> Maybe (Hint, T.Text)
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
    (_, TreeNode [(_, TreeLeaf "quote"), t]) ->
      "'" <> showAsSExp t
    (_, TreeNode [(_, TreeLeaf "unquote"), t]) ->
      "," <> showAsSExp t
    (_, TreeNode [(_, TreeLeaf "quasiquote"), t]) ->
      "`" <> showAsSExp t
    (_, TreeNode [(_, TreeLeaf "quasiunquote"), t]) ->
      "#" <> showAsSExp t
    (_, TreeNode ts) ->
      "(" <> T.intercalate " " (map showAsSExp ts) <> ")"

replaceHint :: Hint -> TreePlus -> TreePlus
replaceHint m tree =
  case tree of
    (m', TreeLeaf x) ->
      (supHint m m', TreeLeaf x)
    (mt, TreeNode ts) -> do
      let ts' = map (replaceHint m) ts
      (supHint m mt, TreeNode ts')
