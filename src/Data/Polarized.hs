module Data.Polarized where

import           Data.Basic

data Pos
  = PosVar Identifier
  | PosConst Identifier
  | PosSigmaIntro [Pos]
  | PosIndexIntro Index
                  LowType
  deriving (Show)

data Neg
  = NegPiElimDownElim Pos
                      Pos
  | NegConstElim Constant
                 [Pos]
  | NegSigmaElim Pos
                 [Identifier]
                 Neg
  | NegIndexElim Pos
                 [(Index, Neg)]
  | NegUpIntro Pos
  | NegUpElim Identifier
              Neg
              Neg
  deriving (Show)

data Constant
  = ConstantArith LowType
                  Arith
  | ConstantPrint LowType
  deriving (Show)
