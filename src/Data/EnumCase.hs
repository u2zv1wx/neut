module Data.EnumCase where

import Data.Meta
import qualified Data.Text as T
import GHC.Generics hiding (Meta)

data EnumCase
  = EnumCaseLabel T.Text
  | EnumCaseDefault
  deriving (Show, Eq, Ord, Generic)

type EnumCasePlus =
  (Meta, EnumCase)
