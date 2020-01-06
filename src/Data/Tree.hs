module Data.Tree where

import Data.Basic

data Tree
  = TreeAtom Identifier
  | TreeNode [TreePlus]
  deriving (Show)

type TreePlus = (TreeMeta, Tree)

newtype TreeMeta =
  TreeMeta
    { treeMetaLocation :: Maybe Loc
    }
  deriving (Show)

emptyTreeMeta :: TreeMeta
emptyTreeMeta = TreeMeta {treeMetaLocation = Nothing}

atomListOf :: TreePlus -> [Identifier]
atomListOf (_, TreeAtom x) = [x]
atomListOf (_, TreeNode ts) = concatMap atomListOf ts
