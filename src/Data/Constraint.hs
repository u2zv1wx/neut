module Data.Constraint where

import qualified Data.HashMap.Strict as Map

import Data.Basic
import Data.WeakTerm

type PreConstraint = (WeakTermPlus, WeakTermPlus)

type IterInfo = (Meta, Identifier, [IdentifierPlus], WeakTermPlus, WeakTermPlus)

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
    Constraint
  deriving (Show)

instance Eq EnrichedConstraint where
  (Enriched _ _ c1) == (Enriched _ _ c2) = c1 == c2

instance Ord EnrichedConstraint where
  compare (Enriched _ _ c1) (Enriched _ _ c2) = compare c1 c2

type SubstWeakTerm' = Map.HashMap Identifier ([Hole], WeakTermPlus)

data UnivLevelPlus =
  UnivLevelPlus Meta UnivLevel

levelOf :: UnivLevelPlus -> UnivLevel
levelOf (UnivLevelPlus _ l) = l

instance Show UnivLevelPlus where
  show (UnivLevelPlus _ l) = "[" ++ show l ++ "]"
  -- show (UnivLevelPlus m l) = "[" ++ show l ++ "]:" ++ showMeta m

instance Eq UnivLevelPlus where
  (UnivLevelPlus _ l1) == (UnivLevelPlus _ l2) = l1 == l2

instance Ord UnivLevelPlus where
  compare (UnivLevelPlus _ l1) (UnivLevelPlus _ l2) = compare l1 l2

type LevelConstraint = (UnivLevelPlus, UnivLevelPlus)

substLevelConstraint ::
     UnivLevelPlus -> UnivLevelPlus -> [LevelConstraint] -> [LevelConstraint]
substLevelConstraint _ _ [] = []
substLevelConstraint from to ((mx, my):cs) = do
  let mx' = substLevelConstraint' from to mx
  let my' = substLevelConstraint' from to my
  let cs' = substLevelConstraint from to cs
  (mx', my') : cs'

substLevelConstraint' ::
     UnivLevelPlus -> UnivLevelPlus -> UnivLevelPlus -> UnivLevelPlus
substLevelConstraint' (UnivLevelPlus _ from) (UnivLevelPlus mTo to) (UnivLevelPlus m x)
  | from == x = UnivLevelPlus (supMeta m mTo) to
  | otherwise = UnivLevelPlus m x
