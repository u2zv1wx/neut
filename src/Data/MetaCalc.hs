module Data.MetaCalc where

import qualified Data.HashMap.Lazy as Map
import Data.Hint
import qualified Data.Text as T

data MetaCalc
  = MetaCalcVar T.Text
  | MetaCalcImpIntro [T.Text] MetaCalcPlus
  | MetaCalcImpElim MetaCalcPlus [MetaCalcPlus]
  | MetaCalcNecIntro MetaCalcPlus
  | MetaCalcNecElim MetaCalcPlus
  | MetaCalcLeaf T.Text
  | MetaCalcNode [MetaCalcPlus]
  deriving (Show)

type MetaCalcPlus =
  (Hint, MetaCalc)

type SubstMetaCalc =
  Map.HashMap T.Text MetaCalcPlus

substMetaCalc :: SubstMetaCalc -> MetaCalcPlus -> MetaCalcPlus
substMetaCalc sub term =
  substMetaCalc' 0 sub term

substMetaCalc' :: Int -> SubstMetaCalc -> MetaCalcPlus -> MetaCalcPlus
substMetaCalc' level sub term =
  case term of
    (_, MetaCalcVar x)
      | level == 0 ->
        case Map.lookup x sub of
          Nothing ->
            term
          Just e ->
            e
      | otherwise ->
        term
    (m, MetaCalcImpIntro xs e)
      | level == 0 -> do
        let sub' = foldr Map.delete sub xs
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
