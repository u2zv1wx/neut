module Data.WeakTerm where

import Numeric.Half

import Data.Basic

data WeakTerm
  = WeakTermTau
  | WeakTermTheta Identifier
  | WeakTermUpsilon Identifier
  | WeakTermPi [IdentifierPlus] WeakTermPlus
  | WeakTermPiIntro [IdentifierPlus] WeakTermPlus
  | WeakTermPiElim WeakTermPlus [WeakTermPlus]
  | WeakTermMu IdentifierPlus WeakTermPlus
  | WeakTermZeta Identifier
  | WeakTermIntS IntSize Integer
  | WeakTermIntU IntSize Integer
  | WeakTermInt Integer
  | WeakTermFloat16 Half
  | WeakTermFloat32 Float
  | WeakTermFloat64 Double
  | WeakTermFloat Double
  | WeakTermEnum EnumType
  | WeakTermEnumIntro EnumValue
  | WeakTermEnumElim WeakTermPlus [(Case, WeakTermPlus)]
  | WeakTermArray
      ArrayKind -- type of elements
      WeakTermPlus -- type of index
  | WeakTermArrayIntro ArrayKind [(EnumValue, WeakTermPlus)]
  | WeakTermArrayElim ArrayKind WeakTermPlus WeakTermPlus
  deriving (Show)

type WeakTermPlus = (WeakMeta, WeakTerm)

type SubstWeakTerm = [(Identifier, WeakTermPlus)]

type Hole = Identifier

type IdentifierPlus = (Identifier, WeakTermPlus)

data WeakMeta
  = WeakMetaTerminal (Maybe Loc)
  | WeakMetaNonTerminal (Maybe Loc)
  deriving (Show) -- data WeakMeta
