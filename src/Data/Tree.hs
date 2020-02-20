module Data.Tree where

import Data.Basic

import qualified Data.Set as S
import qualified Data.Text as T

data Tree
  = TreeAtom T.Text
  | TreeNode [TreePlus]
  deriving (Show)

type TreePlus = (Meta, Tree)

atomListOf :: TreePlus -> S.Set T.Text
atomListOf (_, TreeAtom x) = S.singleton x
atomListOf (_, TreeNode ts) = S.unions $ map atomListOf ts
