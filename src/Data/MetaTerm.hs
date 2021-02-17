module Data.MetaTerm where

import Data.Hint
import Data.Ident
import Data.Int
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
  | MetaTermConst T.Text
  | MetaTermInt64 Int64
  deriving (Show)

type MetaTermPlus =
  (Hint, MetaTerm)

type SubstMetaTerm =
  IntMap.IntMap MetaTermPlus

substMetaTerm :: SubstMetaTerm -> MetaTermPlus -> MetaTermPlus
substMetaTerm sub term =
  case term of
    (_, MetaTermVar x) ->
      case IntMap.lookup (asInt x) sub of
        Nothing ->
          term
        Just e ->
          e
    (m, MetaTermImpIntro xs e) -> do
      let sub' = foldr IntMap.delete sub (map asInt xs)
      let e' = substMetaTerm sub' e
      (m, MetaTermImpIntro xs e')
    (m, MetaTermImpElim e es) -> do
      let e' = substMetaTerm sub e
      let es' = map (substMetaTerm sub) es
      (m, MetaTermImpElim e' es')
    (m, MetaTermNecIntro e) -> do
      let e' = substMetaTerm sub e
      (m, MetaTermNecIntro e')
    (m, MetaTermNecElim e) -> do
      let e' = substMetaTerm sub e
      (m, MetaTermNecElim e')
    (_, MetaTermLeaf _) ->
      term
    (m, MetaTermNode es) -> do
      let es' = map (substMetaTerm sub) es
      (m, MetaTermNode es')
    (_, MetaTermConst _) ->
      term
    (_, MetaTermInt64 _) ->
      term

quote :: MetaTermPlus -> MetaTermPlus
quote (m, t) =
  (m, MetaTermNecIntro (m, t))
