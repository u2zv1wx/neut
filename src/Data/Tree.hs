module Data.Tree where

import Data.Basic

import qualified Data.Set as S

data Tree
  = TreeAtom Identifier
  | TreeNode [TreePlus]
  deriving (Show)

type TreePlus = (Meta, Tree)

atomListOf :: TreePlus -> S.Set Identifier
atomListOf (_, TreeAtom x) = S.singleton x
atomListOf (_, TreeNode ts) = S.unions $ map atomListOf ts
