module Data.Constraint where

import           Data.Basic
import           Data.WeakTerm

type PreConstraint = (WeakTerm, WeakTerm)

data Constraint
  = ConstraintPattern WeakSortal
                      Identifier
                      [WeakTerm]
                      WeakTerm
  | ConstraintQuasiPattern WeakSortal
                           Identifier
                           [WeakTerm]
                           WeakTerm
  | ConstraintFlexRigid WeakSortal
                        Identifier
                        [WeakTerm]
                        WeakTerm
  | ConstraintOther

constraintToInt :: Constraint -> Int
constraintToInt ConstraintPattern {}      = 0
constraintToInt ConstraintQuasiPattern {} = 1
constraintToInt ConstraintFlexRigid {}    = 2
constraintToInt ConstraintOther {}        = 3

instance Eq Constraint where
  c1 == c2 = constraintToInt c1 == constraintToInt c2

instance Ord Constraint where
  compare c1 c2 = compare (constraintToInt c1) (constraintToInt c2)

data EnrichedConstraint =
  Enriched PreConstraint
           [Identifier] -- list of metavariables that cause stuck
           Constraint

instance Eq EnrichedConstraint where
  (Enriched _ _ c1) == (Enriched _ _ c2) = c1 == c2

instance Ord EnrichedConstraint where
  compare (Enriched _ _ c1) (Enriched _ _ c2) = compare c1 c2

compose :: SubstWeakTerm -> SubstWeakTerm -> SubstWeakTerm
compose s1 s2 = do
  let domS2 = map fst s2
  let codS2 = map snd s2
  let codS2' = map (substWeakTerm s1) codS2
  let fromS1 = filter (\(ident, _) -> ident `notElem` domS2) s1
  fromS1 ++ zip domS2 codS2'
