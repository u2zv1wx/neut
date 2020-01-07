module Data.Constraint where

import Data.WeakTerm

type PreConstraint = (WeakTermPlus, WeakTermPlus)

data Constraint
  = ConstraintAnalyzable
  | ConstraintPattern Hole [[WeakTermPlus]] WeakTermPlus
  | ConstraintDelta WeakTermPlus [(PreMeta, [WeakTermPlus])] WeakTermPlus
  | ConstraintQuasiPattern Hole [[WeakTermPlus]] WeakTermPlus
  | ConstraintFlexRigid Hole [[WeakTermPlus]] WeakTermPlus
  | ConstraintOther
  deriving (Show)

constraintToInt :: Constraint -> Int
constraintToInt ConstraintAnalyzable = 0
constraintToInt ConstraintPattern {} = 1
constraintToInt ConstraintDelta {} = 2
constraintToInt ConstraintQuasiPattern {} = 3
constraintToInt ConstraintFlexRigid {} = 4
constraintToInt ConstraintOther = 5

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

type SubstWeakTerm' = [(String, ([Hole], WeakTermPlus))]

-- s1が新たに追加されるsubstで、s2が既存のsubst
-- s1 = m ~> eとして、eのなかにs2でsubstされるべきholeが含まれているとする。
compose :: SubstWeakTerm' -> SubstWeakTerm' -> SubstWeakTerm'
compose s1 s2 = do
  let domS2 = map fst s2
  let codS2 = map snd s2
  let codS2' = map (substIfNecessary s1) codS2
  -- let codS2' = map (substWeakTermPlus s1) codS2
  let s1' = filter (\(ident, _) -> ident `notElem` domS2) s1
  s1' ++ zip domS2 codS2'

substIfNecessary ::
     SubstWeakTerm' -> ([Hole], WeakTermPlus) -> ([Hole], WeakTermPlus)
substIfNecessary sub (hs, e)
  | xs <- map fst sub
  , any (\h -> h `elem` hs) xs = do
    let sub' = map (\(x, (_, body)) -> (x, body)) sub
    let e' = substWeakTermPlus sub' e
    (filter (`notElem` xs) hs, e')
substIfNecessary _ hse = hse
