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
            "LAMBDA"
              | [(_, TreeNode xs), e] <- rest -> do
                xs' <- mapM interpretIdent xs
                e' <- interpretCode e
                return (m, MetaTermImpIntro xs' Nothing e')
              | otherwise ->
                raiseSyntaxError m "(LAMBDA (LEAF*) TREE)"
            "LAMBDA+"
              | [(_, TreeNode args@(_ : _)), e] <- rest -> do
                xs' <- mapM interpretIdent (init args)
                rest' <- interpretIdent $ last args
                e' <- interpretCode e
                return (m, MetaTermImpIntro xs' (Just rest') e')
              | otherwise ->
                raiseSyntaxError m "(LAMBDA+ (LEAF LEAF*) TREE)"
            "APPLY"
              | e : es <- rest -> do
                e' <- interpretCode e
                es' <- mapM (interpretCode) es
                return (m, MetaTermImpElim e' es')
              | otherwise ->
                raiseSyntaxError m "(APPLY TREE TREE*)"
            "FIX"
              | [(_, TreeLeaf f), (_, TreeNode xs), e] <- rest -> do
                xs' <- mapM interpretIdent xs
                e' <- interpretCode e
                return (m, MetaTermFix (asIdent f) xs' Nothing e')
              | otherwise ->
                raiseSyntaxError m "(FIX LEAF (LEAF*) TREE)"
            "FIX+"
              | [(_, TreeLeaf f), (_, TreeNode args@(_ : _)), e] <- rest -> do
                xs' <- mapM interpretIdent (init args)
                rest' <- interpretIdent $ last args
                e' <- interpretCode e
                return (m, MetaTermFix (asIdent f) xs' (Just rest') e')
              | otherwise ->
                raiseSyntaxError m "(FIX+ LEAF (LEAF LEAF*) TREE)"
            "SWITCH"
              | e : cs <- rest -> do
                e' <- interpretCode e
                cs' <- mapM interpretEnumClause cs
                i <- newNameWith' "switch"
                return (m, MetaTermEnumElim (e', i) cs')
              | otherwise ->
                raiseSyntaxError m "(SWITCH TREE TREE*)"
            "quote"
              | [e] <- rest -> do
                e' <- interpretCode e
                return (m, MetaTermImpIntro [] Nothing e')
              | otherwise ->
                raiseSyntaxError m "(quote TREE)"
            "unquote"
              | [e] <- rest -> do
                e' <- interpretCode e
                return (m, MetaTermImpElim e' [])
              | otherwise ->
                raiseSyntaxError m "(unquote TREE)"
            "quasiquote"
              | [e] <- rest ->
                interpretData e
              | otherwise ->
                raiseSyntaxError m "(quasiquote TREE)"
            _ ->
              interpretAux m leaf rest
        leaf : rest ->
          interpretAux m leaf rest

interpretData :: TreePlus -> WithEnv MetaTermPlus
interpretData tree = do
  case tree of
    (m, TreeLeaf atom) ->
      return (m, MetaTermLeaf atom)
    (m, TreeNode treeList) ->
      case treeList of
        (_, TreeLeaf "quasiunquote") : rest
          | [e] <- rest -> do
            interpretCode e
          | otherwise ->
            raiseSyntaxError m "(quasiunquote TREE)"
        _ -> do
          treeList' <- mapM interpretData treeList
          return (m, MetaTermNode treeList')

interpretAux :: Hint -> TreePlus -> [TreePlus] -> WithEnv MetaTermPlus
interpretAux m f args = do
  f' <- interpretCode f
  args' <- mapM interpretCode args
  return (m, MetaTermImpElim f' args')

-- modifyArgs :: MetaTermPlus -> [MetaTermPlus] -> WithEnv [MetaTermPlus]
-- modifyArgs f args = do
--   thunkEnv <- gets autoThunkEnv
--   quoteEnv <- gets autoQuoteEnv
--   case f of
--     (_, MetaTermVar name)
--       | S.member (asText name) thunkEnv ->
--         return $ map wrapWithThunk args
--       | S.member (asText name) quoteEnv ->
--         return $ map wrapWithQuote args
--     _ ->
--       return args

interpretIdent :: TreePlus -> WithEnv Ident
interpretIdent tree =
  case tree of
    (_, TreeLeaf x) ->
      return $ asIdent x
    t ->
      raiseSyntaxError (fst t) "LEAF"

-- wrapWithQuote :: MetaTermPlus -> MetaTermPlus
-- wrapWithQuote (m, t) =
--   (m, MetaTermNode [(m, MetaTermLeaf "quote"), (m, t)])

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
