module Data.Derangement where

import Data.LowType
import qualified Data.Text as T

-- a `derangement` handles an extra-linguistic feature
data Derangement
  = DerangementSyscall Integer
  | DerangementExternal T.Text
  | DerangementLoad LowType
  | DerangementStore LowType
  | DerangementGetElementPtr LowType LowType
  | DerangementCreateArray LowType
  | DerangementCreateStruct [LowType]
  deriving (Show, Eq)

data DerangementArg
  = DerangementArgLinear
  | DerangementArgAffine
  deriving (Show, Eq)
