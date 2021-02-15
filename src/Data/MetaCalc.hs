module Data.MetaCalc where

import Data.Hint
import Data.Ident
import qualified Data.IntMap as IntMap
import qualified Data.Text as T

data MetaCalc
  = MetaCalcVar Ident
  | MetaCalcImpIntro [Ident] MetaCalcPlus
  | MetaCalcImpElim MetaCalcPlus [MetaCalcPlus]
  | MetaCalcNecIntro MetaCalcPlus
  | MetaCalcNecElim MetaCalcPlus
  | MetaCalcLeaf T.Text
  | MetaCalcNode [MetaCalcPlus]
  deriving (Show)

type MetaCalcPlus =
  (Hint, MetaCalc)

type SubstMetaCalc =
  IntMap.IntMap MetaCalcPlus

substMetaCalc :: SubstMetaCalc -> MetaCalcPlus -> MetaCalcPlus
substMetaCalc sub term =
  substMetaCalc' 0 sub term

substMetaCalc' :: Int -> SubstMetaCalc -> MetaCalcPlus -> MetaCalcPlus
substMetaCalc' level sub term =
  case term of
    (_, MetaCalcVar x)
      | level == 0 ->
        case IntMap.lookup (asInt x) sub of
          Nothing ->
            term
          Just e ->
            e
      | otherwise ->
        term
    (m, MetaCalcImpIntro xs e)
      | level == 0 -> do
        let sub' = foldr IntMap.delete sub (map asInt xs)
        let e' = substMetaCalc' level sub' e
        (m, MetaCalcImpIntro xs e')
      | otherwise -> do
        let e' = substMetaCalc' level sub e
        (m, MetaCalcImpIntro xs e')
    (m, MetaCalcImpElim e es) -> do
      let e' = substMetaCalc' level sub e
      let es' = map (substMetaCalc' level sub) es
      (m, MetaCalcImpElim e' es')
    (m, MetaCalcNecIntro e) -> do
      let e' = substMetaCalc' (level - 1) sub e
      (m, MetaCalcNecIntro e')
    (m, MetaCalcNecElim e) -> do
      let e' = substMetaCalc' (level + 1) sub e
      (m, MetaCalcNecIntro e')
    (_, MetaCalcLeaf _) ->
      term
    (m, MetaCalcNode es) -> do
      let es' = map (substMetaCalc' level sub) es
      (m, MetaCalcNode es')
