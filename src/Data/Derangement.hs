module Data.Derangement where

import Data.LowType
import qualified Data.Text as T

data Derangement
  = DerangementSyscall Integer
  | DerangementExternal T.Text
  | DerangementLoad LowType
  | DerangementStore LowType
  deriving (Show, Eq)

data DerangementArg
  = DerangementArgLinear
  | DerangementArgAffine
  deriving (Show, Eq)
