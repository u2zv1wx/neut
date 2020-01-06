module Data.Tree where

import Data.Basic

data Tree
  = TreeAtom Identifier
  | TreeNode [TreePlus]
  deriving (Show)

type TreePlus = (Meta, Tree)

atomListOf :: TreePlus -> [Identifier]
atomListOf (_, TreeAtom x) = [x]
atomListOf (_, TreeNode ts) = concatMap atomListOf ts
