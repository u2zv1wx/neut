module Data.EnumCase where

import Data.Meta
import qualified Data.Text as T

data EnumCase
  = EnumCaseLabel T.Text
  | EnumCaseDefault
  deriving (Show, Eq, Ord)

type EnumCasePlus =
  (Meta, EnumCase)
