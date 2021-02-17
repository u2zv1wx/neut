module Data.MetaTerm where

import Data.EnumCase
import Data.Hint
import Data.Ident
import Data.Int
import qualified Data.IntMap as IntMap
import Data.Maybe (catMaybes)
import qualified Data.Text as T

data MetaTerm
  = MetaTermVar Ident
  | MetaTermImpIntro [Ident] (Maybe Ident) MetaTermPlus
  | MetaTermImpElim MetaTermPlus [MetaTermPlus]
  | MetaTermFix Ident [Ident] (Maybe Ident) MetaTermPlus
  | MetaTermNecIntro MetaTermPlus
  | MetaTermNecElim MetaTermPlus
  | MetaTermLeaf T.Text
  | MetaTermNode [MetaTermPlus]
  | MetaTermConst T.Text
  | MetaTermInt64 Int64
  | MetaTermEnumIntro T.Text
  | MetaTermEnumElim MetaTermPlus [(EnumCasePlus, MetaTermPlus)]
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
    (m, MetaTermImpIntro xs mx e) -> do
      let sub' = foldr IntMap.delete sub (map asInt (xs ++ catMaybes [mx]))
      let e' = substMetaTerm sub' e
      (m, MetaTermImpIntro xs mx e')
    (m, MetaTermImpElim e es) -> do
      let e' = substMetaTerm sub e
      let es' = map (substMetaTerm sub) es
      (m, MetaTermImpElim e' es')
    (m, MetaTermFix f xs mx e) -> do
      let sub' = foldr IntMap.delete sub (map asInt (f : xs ++ catMaybes [mx]))
      let e' = substMetaTerm sub' e
      (m, MetaTermFix f xs mx e')
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
    (_, MetaTermEnumIntro _) ->
      term
    (m, MetaTermEnumElim e ces) -> do
      let e' = substMetaTerm sub e
      let (cs, es) = unzip ces
      let es' = map (substMetaTerm sub) es
      (m, MetaTermEnumElim e' (zip cs es'))

quote :: MetaTermPlus -> MetaTermPlus
quote (m, t) =
  (m, MetaTermNecIntro (m, t))
