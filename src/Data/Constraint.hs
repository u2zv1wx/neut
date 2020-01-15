module Data.Constraint where

import qualified Data.HashMap.Strict as Map

import Data.Basic
import Data.WeakTerm
import Reduce.WeakTerm

type PreConstraint = (WeakTermPlus, WeakTermPlus)

type IterInfo = (Identifier, [IdentifierPlus], WeakTermPlus, WeakTermPlus)

data Constraint
  = ConstraintAnalyzable
  | ConstraintDelta IterInfo [(Meta, [WeakTermPlus])] [(Meta, [WeakTermPlus])]
  | ConstraintQuasiPattern Hole [[WeakTermPlus]] WeakTermPlus
  | ConstraintFlexRigid Hole [[WeakTermPlus]] WeakTermPlus
  | ConstraintOther
  deriving (Show)

constraintToInt :: Constraint -> Int
constraintToInt ConstraintAnalyzable = 0
constraintToInt ConstraintDelta {} = 1
constraintToInt ConstraintQuasiPattern {} = 2
constraintToInt ConstraintFlexRigid {} = 3
constraintToInt ConstraintOther = 4

instance Eq Constraint where
  c1 == c2 = constraintToInt c1 == constraintToInt c2

instance Ord Constraint where
  compare c1 c2 = compare (constraintToInt c1) (constraintToInt c2)

data EnrichedConstraint =
  Enriched
    PreConstraint
    [Hole] -- list of metavariables that cause stuck
    [Hole] -- list of metavariables to be resolved
    Constraint
  deriving (Show)

instance Eq EnrichedConstraint where
  (Enriched _ _ _ c1) == (Enriched _ _ _ c2) = c1 == c2

instance Ord EnrichedConstraint where
  compare (Enriched _ _ _ c1) (Enriched _ _ _ c2) = compare c1 c2

type SubstWeakTerm' = Map.HashMap Identifier ([Hole], WeakTermPlus)
