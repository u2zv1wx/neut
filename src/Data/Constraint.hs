module Data.Constraint where

import           Data.Basic
import           Data.Neut

type PreConstraint = (Neut, Neut)

data Constraint
  = ConstraintPattern Identifier
                      [Identifier]
                      Neut
  | ConstraintBeta Identifier
                   Neut
  | ConstraintDelta Identifier
                    [Neut]
                    [Neut]
  | ConstraintQuasiPattern Identifier
                           [Identifier]
                           Neut
  | ConstraintFlexRigid Identifier
                        [Neut]
                        Neut
  | ConstraintFlexFlex Identifier
                       [Neut]
                       Identifier
                       [Neut]
  deriving (Show)

constraintToInt :: Constraint -> Int
constraintToInt ConstraintPattern {}      = 0
constraintToInt ConstraintDelta {}        = 1
constraintToInt ConstraintBeta {}         = 2
constraintToInt ConstraintQuasiPattern {} = 3
constraintToInt ConstraintFlexRigid {}    = 4
constraintToInt ConstraintFlexFlex {}     = 5

instance Eq Constraint where
  c1 == c2 = constraintToInt c1 == constraintToInt c2

instance Ord Constraint where
  compare c1 c2 = compare (constraintToInt c1) (constraintToInt c2)

data EnrichedConstraint =
  Enriched PreConstraint
           Constraint
  deriving (Show)

instance Eq EnrichedConstraint where
  (Enriched _ c1) == (Enriched _ c2) = c1 == c2

instance Ord EnrichedConstraint where
  compare (Enriched _ c1) (Enriched _ c2) = compare c1 c2
