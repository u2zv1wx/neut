{-# LANGUAGE OverloadedStrings #-}

module Data.Tree where

import Data.Basic

import qualified Data.Set as S
import qualified Data.Text as T

data Tree
  = TreeAtom T.Text
  | TreeNode [TreePlus]
  | TreeNodeSquare [TreePlus]
  deriving (Show)

type TreePlus = (Meta, Tree)

atomListOf :: TreePlus -> S.Set T.Text
atomListOf (_, TreeAtom x) = S.singleton x
atomListOf (_, TreeNode ts) = S.unions $ map atomListOf ts
atomListOf (_, TreeNodeSquare ts) = S.unions $ map atomListOf ts

showAsSExp :: TreePlus -> T.Text
showAsSExp (_, TreeAtom x) = x
showAsSExp (_, TreeNode ts) =
  "(" <> T.intercalate " " (map showAsSExp ts) <> ")"
showAsSExp (_, TreeNodeSquare ts) =
  "[" <> T.intercalate " " (map showAsSExp ts) <> "]"
