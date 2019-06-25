module Data.Constraint where

import           Data.Basic
import           Data.WeakTerm

type PreConstraint = (WeakTerm, WeakTerm)

data Constraint
  = ConstraintPattern WeakSortal
                      Identifier
                      [Identifier]
                      WeakTerm
  | ConstraintBeta Identifier
                   WeakTerm
  | ConstraintDelta Identifier
                    (WeakSortal, [WeakTerm])
                    (WeakSortal, [WeakTerm])
  | ConstraintQuasiPattern WeakSortal
                           Identifier
                           [Identifier]
                           WeakTerm
  | ConstraintFlexRigid WeakSortal
                        Identifier
                        [WeakTerm]
                        WeakTerm
  | ConstraintFlexFlex Identifier
                       (WeakSortal, [WeakTerm])
                       Identifier
                       (WeakSortal, [WeakTerm])

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

instance Eq EnrichedConstraint where
  (Enriched _ c1) == (Enriched _ c2) = c1 == c2

instance Ord EnrichedConstraint where
  compare (Enriched _ c1) (Enriched _ c2) = compare c1 c2

compose :: SubstWeakTerm -> SubstWeakTerm -> SubstWeakTerm
compose s1 s2 = do
  let domS2 = map fst s2
  let codS2 = map snd s2
  let codS2' = map (substWeakTerm s1) codS2
  let fromS1 = filter (\(ident, _) -> ident `notElem` domS2) s1
  fromS1 ++ zip domS2 codS2'
