module Data.MetaTerm where

import Data.Hint
import Data.Ident
import qualified Data.IntMap as IntMap
import qualified Data.Text as T

data MetaTerm
  = MetaTermVar Ident
  | MetaTermImpIntro [Ident] MetaTermPlus
  | MetaTermImpElim MetaTermPlus [MetaTermPlus]
  | MetaTermNecIntro MetaTermPlus
  | MetaTermNecElim MetaTermPlus
  | MetaTermLeaf T.Text
  | MetaTermNode [MetaTermPlus]
  deriving (Show)

type MetaTermPlus =
  (Hint, MetaTerm)

type SubstMetaTerm =
  IntMap.IntMap MetaTermPlus

substMetaTerm :: SubstMetaTerm -> MetaTermPlus -> MetaTermPlus
substMetaTerm sub term =
  substMetaTerm' 0 sub term

substMetaTerm' :: Int -> SubstMetaTerm -> MetaTermPlus -> MetaTermPlus
substMetaTerm' level sub term =
  case term of
    (_, MetaTermVar x)
      | level == 0 ->
        case IntMap.lookup (asInt x) sub of
          Nothing ->
            term
          Just e ->
            e
      | otherwise ->
        term
    (m, MetaTermImpIntro xs e)
      | level == 0 -> do
        let sub' = foldr IntMap.delete sub (map asInt xs)
        let e' = substMetaTerm' level sub' e
        (m, MetaTermImpIntro xs e')
      | otherwise -> do
        let e' = substMetaTerm' level sub e
        (m, MetaTermImpIntro xs e')
    (m, MetaTermImpElim e es) -> do
      let e' = substMetaTerm' level sub e
      let es' = map (substMetaTerm' level sub) es
      (m, MetaTermImpElim e' es')
    (m, MetaTermNecIntro e) -> do
      let e' = substMetaTerm' (level - 1) sub e
      (m, MetaTermNecIntro e')
    (m, MetaTermNecElim e) -> do
      let e' = substMetaTerm' (level + 1) sub e
      (m, MetaTermNecIntro e')
    (_, MetaTermLeaf _) ->
      term
    (m, MetaTermNode es) -> do
      let es' = map (substMetaTerm' level sub) es
      (m, MetaTermNode es')
