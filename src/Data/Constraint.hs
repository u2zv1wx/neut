module Data.Constraint where

import qualified Data.HashMap.Strict as Map

import Data.Basic
import Data.WeakTerm
import Reduce.WeakTerm

type PreConstraint = (WeakTermPlus, WeakTermPlus)

type IterInfo = (String, [IdentifierPlus], WeakTermPlus, WeakTermPlus)

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

type SubstWeakTerm' = Map.HashMap String ([Hole], WeakTermPlus)

-- s1が新たに追加されるsubstで、s2が既存のsubst
-- s1 = m ~> eとして、eのなかにs2でsubstされるべきholeが含まれているとする。
compose :: SubstWeakTerm' -> SubstWeakTerm' -> SubstWeakTerm'
compose s1 s2 = do
  let domS2 = Map.keys s2
  let s2' = Map.map (substIfNecessary s1) s2
  let s1' = Map.filterWithKey (\ident _ -> ident `notElem` domS2) s1
  s1' `Map.union` s2'

substIfNecessary ::
     SubstWeakTerm' -> ([Hole], WeakTermPlus) -> ([Hole], WeakTermPlus)
substIfNecessary sub (hs, e)
  | sub' <- Map.filterWithKey (\x _ -> x `elem` hs) sub
  , not (null sub')
    -- let hs' = concatMap fst $ Map.elems sub'
   = do
    let sub2 = map (\(x, (_, body)) -> (x, body)) $ Map.toList sub
    -- let e' = substWeakTermPlus sub2 e
    -- (hs' ++ filter (`notElem` xs) hs, e')
    let e' = reduceWeakTermPlus $ substWeakTermPlus sub2 e
    (holeWeakTermPlus e', e')
substIfNecessary _ hse = hse
