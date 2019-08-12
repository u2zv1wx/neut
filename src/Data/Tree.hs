{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

module Data.Tree where

import           Control.Comonad.Cofree
import           Text.Show.Deriving

import           Data.Basic

data TreeF a
  = TreeAtom Identifier
  | TreeNode [a]

deriving instance Show a => Show (TreeF a)

deriving instance Functor TreeF

$(deriveShow1 ''TreeF)

type Tree = Cofree TreeF TreeMeta

newtype TreeMeta = TreeMeta
  { treeMetaLocation :: Maybe (Int, Int)
  } deriving (Show)

emptyTreeMeta :: TreeMeta
emptyTreeMeta = TreeMeta {treeMetaLocation = Nothing}
