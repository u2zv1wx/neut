module Preprocess.Interpret
  ( interpretCode,
    interpretEnumItem,
    interpretEnumCase,
  )
where

import Control.Monad.State.Lazy
import Data.EnumCase
import Data.Env
import Data.Hint
import Data.Ident
import Data.Maybe (fromMaybe)
import Data.MetaTerm
import Data.Namespace
import qualified Data.Set as S
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
            "lambda"
              | [(_, TreeNode xs), e] <- rest -> do
                xs' <- mapM interpretIdent xs
                e' <- interpretCode e
                return (m, MetaTermImpIntro xs' Nothing e')
              | otherwise ->
                raiseSyntaxError m "(lambda (LEAF*) TREE)"
            "lambda+"
              | [(_, TreeNode args@(_ : _)), e] <- rest -> do
                xs' <- mapM interpretIdent (init args)
                rest' <- interpretIdent $ last args
                e' <- interpretCode e
                return (m, MetaTermImpIntro xs' (Just rest') e')
              | otherwise ->
                raiseSyntaxError m "(lambda+ (LEAF LEAF*) TREE)"
            "apply"
              | e : es <- rest -> do
                e' <- interpretCode e
                es' <- mapM (interpretCode) es
                return (m, MetaTermImpElim e' es')
              | otherwise ->
                raiseSyntaxError m "(apply TREE TREE*)"
            "fix"
              | [(_, TreeLeaf f), (_, TreeNode xs), e] <- rest -> do
                xs' <- mapM interpretIdent xs
                e' <- interpretCode e
                return (m, MetaTermFix (asIdent f) xs' Nothing e')
              | otherwise ->
                raiseSyntaxError m "(fix LEAF (LEAF*) TREE)"
            "fix+"
              | [(_, TreeLeaf f), (_, TreeNode args@(_ : _)), e] <- rest -> do
                xs' <- mapM interpretIdent (init args)
                rest' <- interpretIdent $ last args
                e' <- interpretCode e
                return (m, MetaTermFix (asIdent f) xs' (Just rest') e')
              | otherwise ->
                raiseSyntaxError m "(fix+ LEAF (LEAF LEAF*) TREE)"
            "switch"
              | e : cs <- rest -> do
                e' <- interpretCode e
                cs' <- mapM interpretEnumClause cs
                i <- newNameWith' "switch"
                return (m, MetaTermEnumElim (e', i) cs')
              | otherwise ->
                raiseSyntaxError m "(switch TREE TREE*)"
            "leaf"
              | [(_, TreeLeaf x)] <- rest -> do
                return (m, MetaTermLeaf x)
              | otherwise ->
                raiseSyntaxError m "(leaf TREE)"
            "node" -> do
              rest' <- mapM interpretCode rest
              return (m, MetaTermNode rest')
            "quote"
              | [e] <- rest -> do
                e' <- interpretData 1 e
                return (m, MetaTermImpIntro [] Nothing e')
              | otherwise ->
                raiseSyntaxError m "(quote TREE)"
            "unquote"
              | [_] <- rest -> do
                raiseSyntaxError m "found an unquote not inside a quote"
              | otherwise ->
                raiseSyntaxError m "(unquote TREE)"
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
        (_, TreeLeaf "quote") : rest
          | [e] <- rest -> do
            e' <- interpretData (level + 1) e
            return (m, MetaTermNode [(m, MetaTermLeaf "quote"), e'])
          | otherwise ->
            raiseSyntaxError m "(quote TREE)"
        (_, TreeLeaf "unquote") : rest
          | [e] <- rest -> do
            if level == 1
              then do
                e' <- interpretCode e
                return (m, MetaTermImpElim e' [])
              else do
                e' <- interpretData (level - 1) e
                return (m, MetaTermNode [(m, MetaTermLeaf "unquote"), e'])
          | otherwise ->
            raiseSyntaxError m "(unquote TREE)"
        _ -> do
          treeList' <- mapM (interpretData level) treeList
          return (m, MetaTermNode treeList')

interpretAux :: Hint -> TreePlus -> [TreePlus] -> WithEnv MetaTermPlus
interpretAux m f args = do
  f' <- interpretCode f
  args' <- modifyArgs f' args
  -- args' <- mapM interpretCode args
  args'' <- mapM interpretCode args'
  return (m, MetaTermImpElim f' args'')

modifyArgs :: MetaTermPlus -> [TreePlus] -> WithEnv [TreePlus]
modifyArgs f args = do
  quoteEnv <- gets autoQuoteEnv
  case f of
    (_, MetaTermVar name)
      | S.member (asText name) quoteEnv ->
        return $ map wrapWithQuote args
    _ ->
      return args

interpretIdent :: TreePlus -> WithEnv Ident
interpretIdent tree =
  case tree of
    (_, TreeLeaf x) ->
      return $ asIdent x
    t ->
      raiseSyntaxError (fst t) "LEAF"

wrapWithQuote :: TreePlus -> TreePlus
wrapWithQuote (m, t) =
  (m, TreeNode [(m, TreeLeaf "quote"), (m, t)])

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
