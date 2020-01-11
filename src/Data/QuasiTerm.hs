module Data.QuasiTerm where

import Numeric.Half

import Data.Basic
-- data QuasiTerm
--   = QuasiTermTau
--   | QuasiTermUpsilon Identifier
--   | QuasiTermPi [IdentifierPlus] QuasiTermPlus
--   | QuasiTermPiIntro [IdentifierPlus] QuasiTermPlus
--   | QuasiTermPiElim QuasiTermPlus [QuasiTermPlus]
--   | QuasiTermIter IdentifierPlus [IdentifierPlus] QuasiTermPlus
--   | QuasiTermZeta Identifier
--   | QuasiTermConst Identifier
--   | QuasiTermConstDecl IdentifierPlus QuasiTermPlus
--   | QuasiTermIntS IntSize Integer
--   | QuasiTermIntU IntSize Integer
--   | QuasiTermInt Integer
--   | QuasiTermFloat16 Half
--   | QuasiTermFloat32 Float
--   | QuasiTermFloat64 Double
--   | QuasiTermFloat Double
--   | QuasiTermEnum EnumType
--   | QuasiTermEnumIntro EnumValue
--   | QuasiTermEnumElim QuasiTermPlus [(Case, QuasiTermPlus)]
--   | QuasiTermArray ArrayKind QuasiTermPlus
--   | QuasiTermArrayIntro ArrayKind [(EnumValue, QuasiTermPlus)]
--   | QuasiTermArrayElim ArrayKind QuasiTermPlus QuasiTermPlus
--   deriving (Show)
-- type QuasiTermPlus = (Meta, QuasiTerm)
-- type Hole = Identifier
-- type IdentifierPlus = (Identifier, QuasiTermPlus)
