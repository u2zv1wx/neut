module Data.Constraint where

import Data.Basic
import Data.WeakTerm

type PreConstraint = (WeakTermPlus, WeakTermPlus)

type IterInfo = (Meta, Identifier, [IdentifierPlus], WeakTermPlus, WeakTermPlus)

data Constraint
  = ConstraintAnalyzable
  | ConstraintQuasiPattern Hole [[WeakTermPlus]] WeakTermPlus
  | ConstraintFlexRigid Hole [[WeakTermPlus]] WeakTermPlus
  | ConstraintOther
  deriving (Show)

constraintToInt :: Constraint -> Int
constraintToInt ConstraintAnalyzable = 0
constraintToInt ConstraintQuasiPattern {} = 1
constraintToInt ConstraintFlexRigid {} = 2
constraintToInt ConstraintOther = 3

instance Eq Constraint where
  c1 == c2 = constraintToInt c1 == constraintToInt c2

instance Ord Constraint where
  compare c1 c2 = compare (constraintToInt c1) (constraintToInt c2)

data EnrichedConstraint =
  Enriched
    PreConstraint
    [Hole] -- list of metavariables that cause stuck
    Constraint
  deriving (Show)

instance Eq EnrichedConstraint where
  (Enriched _ _ c1) == (Enriched _ _ c2) = c1 == c2

instance Ord EnrichedConstraint where
  compare (Enriched _ _ c1) (Enriched _ _ c2) = compare c1 c2

type LevelConstraint = (UnivLevelPlus, (Integer, UnivLevelPlus))
