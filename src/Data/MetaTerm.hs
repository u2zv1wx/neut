{-# LANGUAGE DeriveGeneric #-}

module Data.MetaTerm where

import Data.EnumCase
import Data.Hashable
import Data.Hint
import Data.Ident
import Data.Int
import qualified Data.IntMap as IntMap
import Data.Maybe (catMaybes)
import qualified Data.PQueue.Min as Q
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Tree
import GHC.Generics (Generic)

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
  | MetaTermEnumElim (MetaTermPlus, Ident) [(EnumCasePlus, MetaTermPlus)]
  deriving (Show)

type MetaTermPlus =
  (Hint, MetaTerm)

-- HM
data MetaType
  = MetaTypeVar Ident
  | MetaTypeArrow [MetaTypePlus] MetaTypePlus
  | MetaTypeNec MetaTypePlus
  | MetaTypeInt64
  | MetaTypeAST
  | MetaTypeEnum T.Text
  deriving (Show)

type MetaTypePlus =
  (Hint, MetaType)

-- type MetaConstraint =
--   (MetaTypePlus, MetaTypePlus)

data MetaConstraint
  = MetaConstraintUnprocessed MetaTypePlus MetaTypePlus
  | MetaConstraintProcessed MetaTypePlus MetaTypePlus
  deriving (Show)

metaConstraintToInt :: MetaConstraint -> Int
metaConstraintToInt c =
  case c of
    MetaConstraintUnprocessed {} ->
      0
    MetaConstraintProcessed {} ->
      1

data Level
  = LevelMono Int
  | LevelPoly
  deriving (Show, Eq, Generic)

baseLevel :: Int
baseLevel =
  1

instance Hashable Level

instance Eq MetaConstraint where
  c1 == c2 =
    metaConstraintToInt c1 == metaConstraintToInt c2

instance Ord MetaConstraint where
  compare c1 c2 =
    compare (metaConstraintToInt c1) (metaConstraintToInt c2)

type MetaConstraintQueue =
  Q.MinQueue MetaConstraint

metaTypeToText :: MetaTypePlus -> T.Text
metaTypeToText t =
  showAsSExp $ metaTypeToTree t

metaTypeToTree :: MetaTypePlus -> TreePlus
metaTypeToTree t =
  case t of
    (m, MetaTypeVar x) ->
      (m, TreeLeaf $ "?M" <> T.pack (show $ asInt x))
    -- (m, TreeLeaf $ asText' x)
    (m, MetaTypeArrow domList cod) -> do
      let domList' = map metaTypeToTree domList
      let cod' = metaTypeToTree cod
      (m, TreeNode [(m, TreeLeaf "arrow"), (m, TreeNode domList'), cod'])
    (m, MetaTypeNec t') -> do
      let t'' = metaTypeToTree t'
      (m, TreeNode [(m, TreeLeaf "box"), t''])
    (m, MetaTypeInt64) -> do
      (m, TreeLeaf "i64")
    (m, MetaTypeAST) -> do
      (m, TreeLeaf "code")
    (m, MetaTypeEnum c) -> do
      (m, TreeLeaf c)

type SubstMetaType =
  IntMap.IntMap MetaTypePlus

type MetaTypeEnv =
  IntMap.IntMap ([Int], MetaTypePlus)

substMetaType :: SubstMetaType -> MetaTypePlus -> MetaTypePlus
substMetaType sub t =
  case t of
    (_, MetaTypeVar x) ->
      case IntMap.lookup (asInt x) sub of
        Just t' ->
          t'
        Nothing ->
          t
    (m, MetaTypeArrow domList cod) -> do
      let domList' = map (substMetaType sub) domList
      let cod' = substMetaType sub cod
      (m, MetaTypeArrow domList' cod')
    (m, MetaTypeNec t') ->
      (m, MetaTypeNec (substMetaType sub t'))
    _ ->
      t

embed :: TreePlus -> MetaTermPlus
embed term =
  case term of
    (m, TreeLeaf x) ->
      (m, MetaTermLeaf x)
    (m, TreeNode es) ->
      (m, MetaTermNode (map embed es))

type SubstMetaTerm =
  IntMap.IntMap MetaTermPlus

varMetaType :: MetaTypePlus -> S.Set Ident
varMetaType t =
  case t of
    (_, MetaTypeVar x) ->
      S.singleton x
    (_, MetaTypeArrow ts cod) -> do
      S.unions $ map varMetaType $ cod : ts
    (_, MetaTypeNec t') ->
      varMetaType t'
    _ ->
      S.empty

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
    (m, MetaTermEnumElim (e, i) ces) -> do
      let e' = substMetaTerm sub e
      let (cs, es) = unzip ces
      let es' = map (substMetaTerm sub) es
      (m, MetaTermEnumElim (e', i) (zip cs es'))

quote :: MetaTermPlus -> MetaTermPlus
quote (m, t) =
  (m, MetaTermNecIntro (m, t))

toTree :: MetaTermPlus -> TreePlus
toTree term =
  case term of
    (m, MetaTermVar x) ->
      (m, TreeLeaf $ asText' x) -- ホントはmeta専用の名前にするべき
    (m, MetaTermImpIntro xs Nothing e) -> do
      let e' = toTree e
      let xs' = map (\i -> (m, TreeLeaf $ asText' i)) xs
      (m, TreeNode [(m, TreeLeaf "lambda"), (m, TreeNode xs'), e'])
    (m, MetaTermImpIntro xs (Just rest) e) -> do
      let e' = toTree e
      let args = map (\i -> (m, TreeLeaf $ asText' i)) $ xs ++ [rest]
      (m, TreeNode [(m, TreeLeaf "lambda+"), (m, TreeNode args), e'])
    (m, MetaTermImpElim e es) -> do
      let e' = toTree e
      let es' = map toTree es
      (m, TreeNode (e' : es'))
    -- (m, TreeNode ((m, TreeLeaf "apply") : e' : es'))
    (m, MetaTermFix f xs Nothing e) -> do
      let e' = toTree e
      let xs' = map (\i -> (m, TreeLeaf $ asText' i)) xs
      (m, TreeNode [(m, TreeLeaf "fix"), (m, TreeLeaf (asText' f)), (m, TreeNode xs'), e'])
    (m, MetaTermFix f xs (Just rest) e) -> do
      let e' = toTree e
      let args = map (\i -> (m, TreeLeaf $ asText' i)) $ xs ++ [rest]
      (m, TreeNode [(m, TreeLeaf "fix+"), (m, TreeLeaf (asText' f)), (m, TreeNode args), e'])
    (m, MetaTermNecIntro e) -> do
      let e' = toTree e
      (m, TreeNode [(m, TreeLeaf "quote"), e'])
    (m, MetaTermNecElim e) -> do
      let e' = toTree e
      (m, TreeNode [(m, TreeLeaf "unquote"), e'])
    (m, MetaTermLeaf x) ->
      (m, TreeLeaf x)
    (m, MetaTermNode es) -> do
      let es' = map toTree es
      (m, TreeNode es')
    (m, MetaTermConst c) ->
      (m, TreeLeaf c)
    (m, MetaTermInt64 i) ->
      (m, TreeLeaf $ T.pack $ show i)
    (m, MetaTermEnumIntro a) ->
      (m, TreeLeaf a)
    (m, MetaTermEnumElim (e, _) caseList) -> do
      let e' = toTree e
      let (cs, bodyList) = unzip caseList
      let cs' = map toTreeEnumCase cs
      let bodyList' = map toTree bodyList
      let caseList' = map (\(c, body) -> (m, TreeNode [c, body])) $ zip cs' bodyList'
      (m, TreeNode [(m, TreeLeaf "switch"), e', (m, TreeNode caseList')])

toTreeEnumCase :: EnumCasePlus -> TreePlus
toTreeEnumCase (m, v) =
  case v of
    EnumCaseLabel l ->
      (m, TreeLeaf l)
    EnumCaseDefault ->
      (m, TreeLeaf "default")
