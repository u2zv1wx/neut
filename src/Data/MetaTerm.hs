module Data.MetaTerm where

import Data.Basic
import qualified Data.HashMap.Lazy as Map
import Data.Int
import qualified Data.IntMap as IntMap
import Data.Maybe (catMaybes)
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

type SubstMetaTerm =
  IntMap.IntMap MetaTermPlus

-- これをmetaconstantsの中で使って引数の形を指定する
data Arg
  = ArgLeaf
  | ArgNode
  | ArgInt
  | ArgEnum
  | ArgLam
  | ArgAny
  deriving (Ord, Eq, Show)

embed :: TreePlus -> MetaTermPlus
embed term =
  case term of
    (m, TreeLeaf x) ->
      (m, MetaTermLeaf x)
    (m, TreeNode es) ->
      (m, MetaTermNode (map embed es))

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

showMetaTerm :: MetaTermPlus -> T.Text
showMetaTerm e =
  showAsSExp (toTree e)

toTree :: MetaTermPlus -> TreePlus
toTree term =
  case term of
    (m, MetaTermVar x) ->
      (m, TreeLeaf $ asText' x) -- ホントはmeta専用の名前にするべき
    (m, MetaTermImpIntro xs Nothing e) -> do
      let e' = toTree e
      let xs' = map (\i -> (m, TreeLeaf $ asText' i)) xs
      (m, TreeNode [(m, TreeLeaf "lambda-meta"), (m, TreeNode xs'), e'])
    (m, MetaTermImpIntro xs (Just rest) e) -> do
      let e' = toTree e
      let args = map (\i -> (m, TreeLeaf $ asText' i)) $ xs ++ [rest]
      (m, TreeNode [(m, TreeLeaf "lambda-meta-variadic"), (m, TreeNode args), e'])
    (m, MetaTermImpElim e es) -> do
      let e' = toTree e
      let es' = map toTree es
      (m, TreeNode ((m, TreeLeaf "apply-meta") : e' : es'))
    (m, MetaTermFix f xs Nothing e) -> do
      let e' = toTree e
      let xs' = map (\i -> (m, TreeLeaf $ asText' i)) xs
      (m, TreeNode [(m, TreeLeaf "fix-meta"), (m, TreeLeaf (asText' f)), (m, TreeNode xs'), e'])
    (m, MetaTermFix f xs (Just rest) e) -> do
      let e' = toTree e
      let args = map (\i -> (m, TreeLeaf $ asText' i)) $ xs ++ [rest]
      (m, TreeNode [(m, TreeLeaf "fix-meta-variadic"), (m, TreeLeaf (asText' f)), (m, TreeNode args), e'])
    (m, MetaTermLeaf x) ->
      (m, TreeNode [(m, TreeLeaf "leaf"), (m, TreeLeaf x)])
    -- (m, TreeLeaf x)
    (m, MetaTermNode es) -> do
      let es' = map toTree es
      (m, TreeNode ((m, TreeLeaf "node") : es'))
    -- (m, TreeNode es')
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
      (m, TreeNode [(m, TreeLeaf "switch-meta"), e', (m, TreeNode caseList')])

toTreeEnumCase :: EnumCasePlus -> TreePlus
toTreeEnumCase (m, v) =
  case v of
    EnumCaseLabel l ->
      (m, TreeLeaf l)
    EnumCaseDefault ->
      (m, TreeLeaf "default")

showArgForm :: Arg -> T.Text
showArgForm arg =
  case arg of
    ArgLeaf ->
      "leaf"
    ArgNode ->
      "node"
    ArgInt ->
      "int"
    ArgEnum ->
      "enum"
    ArgLam ->
      "lambda-term"
    ArgAny ->
      "(any)"

metaConstants :: Map.HashMap T.Text [Arg]
metaConstants =
  Map.unions [metaTreeConstants, metaArithConstants, metaCmpConstants]

metaTreeConstants :: Map.HashMap T.Text [Arg]
metaTreeConstants =
  Map.fromList
    [ ("cons", [ArgAny, ArgNode]),
      ("dump", [ArgAny]),
      ("head", [ArgNode]),
      ("is-leaf", [ArgAny]),
      ("is-nil", [ArgNode]),
      ("is-node", [ArgAny]),
      ("leaf-equal", [ArgLeaf, ArgLeaf]),
      ("leaf-mul", [ArgLeaf, ArgLeaf]),
      ("leaf-uncons", [ArgLeaf]),
      ("string-to-u8-list", [ArgLeaf]),
      ("new-symbol", []),
      ("nth", [ArgInt, ArgNode]),
      ("tail", [ArgNode])
    ]

metaArithConstants :: Map.HashMap T.Text [Arg]
metaArithConstants =
  Map.fromList
    [ ("int-add", [ArgInt, ArgInt]),
      ("int-sub", [ArgInt, ArgInt]),
      ("int-mul", [ArgInt, ArgInt]),
      ("int-div", [ArgInt, ArgInt])
    ]

metaCmpConstants :: Map.HashMap T.Text [Arg]
metaCmpConstants =
  Map.fromList
    [ ("int-gt", [ArgInt, ArgInt]),
      ("int-ge", [ArgInt, ArgInt]),
      ("int-lt", [ArgInt, ArgInt]),
      ("int-le", [ArgInt, ArgInt]),
      ("int-eq", [ArgInt, ArgInt])
    ]
