module Data.EnumCase where

import Data.Hint
import qualified Data.Text as T

data EnumCase
  = EnumCaseLabel T.Text
  | EnumCaseDefault
  deriving (Show, Eq, Ord)

type EnumCasePlus =
  (Hint, EnumCase)
