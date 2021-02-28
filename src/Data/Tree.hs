module Data.Tree where

import Data.Basic
import qualified Data.Text as T

data Tree
  = TreeLeaf T.Text
  | TreeNode [TreePlus]
  deriving (Show)

type TreePlus =
  (Hint, Tree)

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
