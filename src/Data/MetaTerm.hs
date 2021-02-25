module Data.MetaTerm where

import Data.EnumCase
import Data.Hint
import Data.Ident
import Data.Int
import qualified Data.IntMap as IntMap
import Data.Maybe (catMaybes)
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Tree

-- untyped lambda calculus with AST values (node / leaf)
data MetaTerm
  = MetaTermVar Ident
  | MetaTermImpIntro [Ident] (Maybe Ident) MetaTermPlus
  | MetaTermImpElim MetaTermPlus [MetaTermPlus]
  | MetaTermFix Ident [Ident] (Maybe Ident) MetaTermPlus
  | MetaTermLeaf T.Text
  | MetaTermNode [MetaTermPlus]
  | MetaTermConst T.Text
  | MetaTermInt64 Int64
  | MetaTermEnumIntro T.Text
  | MetaTermEnumElim (MetaTermPlus, Ident) [(EnumCasePlus, MetaTermPlus)]
  deriving (Show)

type MetaTermPlus =
  (Hint, MetaTerm)

embed :: TreePlus -> MetaTermPlus
embed term =
  case term of
    (m, TreeLeaf x) ->
      (m, MetaTermLeaf x)
    (m, TreeNode es) ->
      (m, MetaTermNode (map embed es))

type SubstMetaTerm =
  IntMap.IntMap MetaTermPlus

substMetaTerm :: SubstMetaTerm -> MetaTermPlus -> MetaTermPlus
substMetaTerm sub term =
  case term of
    (m, MetaTermVar x) ->
      case IntMap.lookup (asInt x) sub of
        Nothing ->
          term
        Just (_, e) ->
          (m, e)
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
      -- (m, TreeNode (e' : es'))
      (m, TreeNode ((m, TreeLeaf "expand") : e' : es'))
    (m, MetaTermFix f xs Nothing e) -> do
      let e' = toTree e
      let xs' = map (\i -> (m, TreeLeaf $ asText' i)) xs
      (m, TreeNode [(m, TreeLeaf "fix"), (m, TreeLeaf (asText' f)), (m, TreeNode xs'), e'])
    (m, MetaTermFix f xs (Just rest) e) -> do
      let e' = toTree e
      let args = map (\i -> (m, TreeLeaf $ asText' i)) $ xs ++ [rest]
      (m, TreeNode [(m, TreeLeaf "fix+"), (m, TreeLeaf (asText' f)), (m, TreeNode args), e'])
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

metaConstants :: S.Set T.Text
metaConstants =
  S.fromList
    [ "cons",
      "dump",
      "evaluate",
      "is-nil",
      "head",
      "tail",
      "leaf-equal",
      "is-leaf",
      "is-node",
      "leaf-mul",
      "leaf-uncons",
      "new-symbol",
      "nth",
      "int-add",
      "int-sub",
      "int-mul",
      "int-div",
      "int-eq",
      "int-gt",
      "int-ge",
      "int-le",
      "int-lt"
    ]
