module Data.Comp where

import Data.Basic
import qualified Data.IntMap as IntMap
import Data.LowType
import qualified Data.Text as T

data Value
  = ValueConst T.Text
  | ValueUpsilon Ident
  | ValueSigmaIntro [ValuePlus]
  | ValueInt IntSize Integer
  | ValueFloat FloatSize Double
  | ValueEnumIntro T.Text
  deriving (Show)

data Comp
  = CompPrimitive Primitive
  | CompPiElimDownElim ValuePlus [ValuePlus] -- ((force v) v1 ... vn)
  | CompSigmaElim [Ident] ValuePlus CompPlus
  | CompUpIntro ValuePlus
  | CompUpElim Ident CompPlus CompPlus
  | CompEnumElim ValuePlus [(EnumCase, CompPlus)]
  deriving (Show)

data Primitive
  = PrimitivePrimOp PrimOp [ValuePlus]
  | PrimitiveDerangement Derangement [ValuePlus]
  deriving (Show)

newtype IsFixed
  = IsFixed Bool
  deriving (Show)

data Definition
  = Definition IsFixed [Ident] CompPlus
  deriving (Show)

type ValuePlus =
  (Hint, Value)

type CompPlus =
  (Hint, Comp)

type SubstValuePlus =
  IntMap.IntMap ValuePlus

asUpsilon :: ValuePlus -> Maybe Ident
asUpsilon term =
  case term of
    (_, ValueUpsilon x) ->
      Just x
    _ ->
      Nothing
