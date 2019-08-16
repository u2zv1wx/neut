module Data.Tree where

import           Data.Basic

data Tree
  = TreeAtom Identifier
  | TreeNode [TreePlus]
  deriving (Show)

type TreePlus = (TreeMeta, Tree)

newtype TreeMeta = TreeMeta
  { treeMetaLocation :: Maybe (Int, Int)
  } deriving (Show)

emptyTreeMeta :: TreeMeta
emptyTreeMeta = TreeMeta {treeMetaLocation = Nothing}
