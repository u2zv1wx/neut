module Data.Constraint where

import Data.Hint
import Data.Ident
import qualified Data.PQueue.Min as Q
import qualified Data.Set as S
import Data.WeakTerm

type ConstraintQueue =
  Q.MinQueue EnrichedConstraint

type PreConstraint =
  (WeakTermPlus, WeakTermPlus)

type FixInfo =
  (Hint, Ident, [WeakIdentPlus], WeakTermPlus, WeakTermPlus)

data Constraint
  = ConstraintAnalyzable
  | ConstraintQuasiPattern Int [[WeakTermPlus]] WeakTermPlus
  | ConstraintFlexRigid Int [[WeakTermPlus]] WeakTermPlus
  | ConstraintOther
  deriving (Show)

constraintToInt :: Constraint -> Int
constraintToInt c =
  case c of
    ConstraintAnalyzable {} ->
      0
    ConstraintQuasiPattern {} ->
      1
    ConstraintFlexRigid {} ->
      2
    ConstraintOther {} ->
      3

instance Eq Constraint where
  c1 == c2 =
    constraintToInt c1 == constraintToInt c2

instance Ord Constraint where
  compare c1 c2 =
    compare (constraintToInt c1) (constraintToInt c2)

data EnrichedConstraint
  = Enriched
      PreConstraint
      (S.Set Int) -- the set of the metavariables that cause stuck
      Constraint
  deriving (Show)

instance Eq EnrichedConstraint where
  (Enriched _ _ c1) == (Enriched _ _ c2) =
    c1 == c2

instance Ord EnrichedConstraint where
  compare (Enriched _ _ c1) (Enriched _ _ c2) =
    compare c1 c2
