module Preprocess.Interpret
  ( interpretCode,
    interpretEnumItem,
    interpretEnumCase,
  )
where

import Data.EnumCase
import Data.Env
import Data.Hint
import Data.Ident
import Data.Maybe (fromMaybe)
import Data.MetaTerm
import Data.Namespace
import qualified Data.Text as T
import Data.Tree
import Text.Read (readMaybe)

interpretCode :: TreePlus -> WithEnv MetaTermPlus
interpretCode tree =
  case tree of
    (m, TreeLeaf atom)
      | Just i <- readMaybe $ T.unpack atom ->
        return (m, MetaTermInt64 i)
      | otherwise ->
        return (m, MetaTermVar $ asIdent atom)
    (m, TreeNode treeList) ->
      case treeList of
        [] ->
          raiseSyntaxError m "(TREE TREE*)"
        leaf@(_, TreeLeaf headAtom) : rest -> do
          case headAtom of
            "lambda-meta"
              | [(_, TreeNode xs), e] <- rest -> do
                xs' <- mapM interpretIdent xs
                e' <- interpretCode e
                return (m, MetaTermImpIntro xs' Nothing e')
              | otherwise ->
                raiseSyntaxError m "(lambda-meta (LEAF*) TREE)"
            "lambda-meta-variadic"
              | [(_, TreeNode args@(_ : _)), e] <- rest -> do
                xs' <- mapM interpretIdent (init args)
                rest' <- interpretIdent $ last args
                e' <- interpretCode e
                return (m, MetaTermImpIntro xs' (Just rest') e')
              | otherwise ->
                raiseSyntaxError m "(lambda-meta-variadic (LEAF LEAF*) TREE)"
            "apply-meta"
              | e : es <- rest -> do
                interpretAux m e es
              | otherwise ->
                raiseSyntaxError m "(apply-meta TREE TREE*)"
            "fix-meta"
              | [(_, TreeLeaf f), (_, TreeNode xs), e] <- rest -> do
                xs' <- mapM interpretIdent xs
                e' <- interpretCode e
                return (m, MetaTermFix (asIdent f) xs' Nothing e')
              | otherwise ->
                raiseSyntaxError m "(fix-meta LEAF (LEAF*) TREE)"
            "fix-meta-variadic"
              | [(_, TreeLeaf f), (_, TreeNode args@(_ : _)), e] <- rest -> do
                xs' <- mapM interpretIdent (init args)
                rest' <- interpretIdent $ last args
                e' <- interpretCode e
                return (m, MetaTermFix (asIdent f) xs' (Just rest') e')
              | otherwise ->
                raiseSyntaxError m "(fix-meta-variadic LEAF (LEAF LEAF*) TREE)"
            "switch-meta"
              | e : cs <- rest -> do
                e' <- interpretCode e
                cs' <- mapM interpretEnumClause cs
                i <- newNameWith' "switch"
                return (m, MetaTermEnumElim (e', i) cs')
              | otherwise ->
                raiseSyntaxError m "(switch-meta TREE TREE*)"
            "leaf"
              | [(_, TreeLeaf x)] <- rest -> do
                return (m, MetaTermLeaf x)
              | otherwise ->
                raiseSyntaxError m "(leaf TREE)"
            "node" -> do
              rest' <- mapM interpretCode rest
              return (m, MetaTermNode rest')
            "quasiquote"
              | [e] <- rest -> do
                interpretData 1 e
              | otherwise ->
                raiseSyntaxError m "(quasiquote TREE)"
            "quasiunquote"
              | [_] <- rest -> do
                raiseSyntaxError m "found a quasiunquote not inside a quote"
              | otherwise ->
                raiseSyntaxError m "(quasiunquote TREE)"
            "begin-meta" -> do
              let x = (m, TreeLeaf "x")
              let k = (m, TreeLeaf "k")
              let lam = (m, TreeLeaf "lambda-meta")
              let bind = (m, TreeNode [lam, (m, TreeNode [x, k]), (m, TreeNode [k, x])])
              interpretWith (m, TreeNode ((m, TreeLeaf "with-meta") : bind : rest))
            "with-meta" ->
              interpretWith tree
            _ ->
              interpretAux m leaf rest
        leaf : rest ->
          interpretAux m leaf rest

interpretData :: Int -> TreePlus -> WithEnv MetaTermPlus
interpretData level tree = do
  case tree of
    (m, TreeLeaf atom) ->
      return (m, MetaTermLeaf atom)
    (m, TreeNode treeList) ->
      case treeList of
        (_, TreeLeaf "quasiquote") : rest
          | [e] <- rest -> do
            e' <- interpretData (level + 1) e
            return (m, MetaTermNode [(m, MetaTermLeaf "quasiquote"), e'])
          | otherwise ->
            raiseSyntaxError m "(quote TREE)"
        (_, TreeLeaf "quasiunquote") : rest
          | [e] <- rest -> do
            if level == 1
              then interpretCode e
              else do
                e' <- interpretData (level - 1) e
                return (m, MetaTermNode [(m, MetaTermLeaf "quasiunquote"), e'])
          | otherwise ->
            raiseSyntaxError m "(quasiunquote TREE)"
        _ -> do
          treeList' <- mapM (interpretData level) treeList
          return (m, MetaTermNode treeList')

interpretAux :: Hint -> TreePlus -> [TreePlus] -> WithEnv MetaTermPlus
interpretAux m f args = do
  f' <- interpretCode f
  args' <- mapM interpretCode args
  return (m, MetaTermImpElim f' args')

interpretIdent :: TreePlus -> WithEnv Ident
interpretIdent tree =
  case tree of
    (_, TreeLeaf x) ->
      return $ asIdent x
    t ->
      raiseSyntaxError (fst t) "LEAF"

interpretEnumItem :: Hint -> T.Text -> [TreePlus] -> WithEnv [(T.Text, Int)]
interpretEnumItem m name ts = do
  xis <- interpretEnumItem' name $ reverse ts
  if isLinear (map snd xis)
    then return $ reverse xis
    else raiseError m "found a collision of discriminant"

interpretEnumItem' :: T.Text -> [TreePlus] -> WithEnv [(T.Text, Int)]
interpretEnumItem' name treeList =
  case treeList of
    [] ->
      return []
    [t] -> do
      (s, mj) <- interpretEnumItem'' t
      return [(name <> nsSep <> s, fromMaybe 0 mj)]
    (t : ts) -> do
      ts' <- interpretEnumItem' name ts
      (s, mj) <- interpretEnumItem'' t
      return $ (name <> nsSep <> s, fromMaybe (1 + headDiscriminantOf ts') mj) : ts'

interpretEnumItem'' :: TreePlus -> WithEnv (T.Text, Maybe Int)
interpretEnumItem'' tree =
  case tree of
    (_, TreeLeaf s) ->
      return (s, Nothing)
    (_, TreeNode [(_, TreeLeaf s), (_, TreeLeaf i)])
      | Just i' <- readMaybe $ T.unpack i ->
        return (s, Just i')
    t ->
      raiseSyntaxError (fst t) "LEAF | (LEAF LEAF)"

headDiscriminantOf :: [(T.Text, Int)] -> Int
headDiscriminantOf labelNumList =
  case labelNumList of
    [] ->
      0
    ((_, i) : _) ->
      i

interpretEnumClause :: TreePlus -> WithEnv (EnumCasePlus, MetaTermPlus)
interpretEnumClause tree =
  case tree of
    (_, TreeNode [c, e]) -> do
      c' <- interpretEnumCase c
      e' <- interpretCode e
      return (c', e')
    e ->
      raiseSyntaxError (fst e) "(TREE TREE)"

interpretEnumCase :: TreePlus -> WithEnv EnumCasePlus
interpretEnumCase tree =
  case tree of
    (m, TreeNode [(_, TreeLeaf "enum-introduction"), (_, TreeLeaf l)]) ->
      return (m, EnumCaseLabel l)
    (m, TreeLeaf "default") ->
      return (m, EnumCaseDefault)
    (m, TreeLeaf l) ->
      return (m, EnumCaseLabel l)
    (m, _) ->
      raiseSyntaxError m "default | LEAF"

interpretWith :: TreePlus -> WithEnv MetaTermPlus
interpretWith tree =
  case tree of
    (m, TreeNode (with@(_, TreeLeaf "with-meta") : bind : (_, TreeNode ((_, TreeLeaf "let") : xt : es)) : rest)) -> do
      bind' <- interpretCode bind
      e' <- interpretWith (m, TreeNode (with : bind : es))
      xt' <- interpretIdent xt
      rest' <- interpretWith (m, TreeNode (with : bind : rest))
      return (m, MetaTermImpElim bind' [e', (m, MetaTermImpIntro [xt'] Nothing rest')])
    (_, TreeNode [(_, TreeLeaf "with-meta"), _, e]) ->
      interpretCode e
    (m, TreeNode (with@(_, TreeLeaf "with-meta") : bind : e : rest)) -> do
      let e' = (m, TreeNode [(m, TreeLeaf "let"), (m, TreeLeaf "_"), e]) -- fixme: "_"
      interpretWith (m, TreeNode (with : bind : e' : rest))
    t ->
      raiseSyntaxError (fst t) "(with-meta TREE TREE+)"
