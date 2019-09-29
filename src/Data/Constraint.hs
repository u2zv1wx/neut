module Data.Constraint where

import Data.WeakTerm

type PreConstraint = (WeakTermPlus, WeakTermPlus)

data Constraint
  = ConstraintImmediate Hole WeakTermPlus
  | ConstraintPattern Hole [[WeakTermPlus]] WeakTermPlus
  | ConstraintQuasiPattern Hole [[WeakTermPlus]] WeakTermPlus
  | ConstraintFlexRigid Hole [[WeakTermPlus]] WeakTermPlus
  | ConstraintFlexFlex Hole [[WeakTermPlus]] WeakTermPlus
  | ConstraintOther

constraintToInt :: Constraint -> Int
constraintToInt ConstraintImmediate {} = 0
constraintToInt ConstraintPattern {} = 1
constraintToInt ConstraintQuasiPattern {} = 2
constraintToInt ConstraintFlexRigid {} = 3
constraintToInt ConstraintFlexFlex {} = 4
constraintToInt ConstraintOther {} = 5

instance Eq Constraint where
  c1 == c2 = constraintToInt c1 == constraintToInt c2

instance Ord Constraint where
  compare c1 c2 = compare (constraintToInt c1) (constraintToInt c2)

data EnrichedConstraint =
  Enriched
    PreConstraint
    [Hole] -- list of metavariables that cause stuck
    Constraint

instance Eq EnrichedConstraint where
  (Enriched _ _ c1) == (Enriched _ _ c2) = c1 == c2

instance Ord EnrichedConstraint where
  compare (Enriched _ _ c1) (Enriched _ _ c2) = compare c1 c2

compose :: SubstWeakTerm -> SubstWeakTerm -> SubstWeakTerm
compose s1 s2 = do
  let domS2 = map fst s2
  let codS2 = map snd s2
  let codS2' = map (substWeakTermPlus s1) codS2
  let fromS1 = filter (\(ident, _) -> ident `notElem` domS2) s1
  fromS1 ++ zip domS2 codS2'
