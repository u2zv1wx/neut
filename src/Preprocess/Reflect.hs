module Preprocess.Reflect
  ( reflect,
    reflectEnumItem,
    reflectEnumCase,
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

reflect :: TreePlus -> WithEnv MetaTermPlus
reflect tree =
  reflect' 1 tree

reflect' :: Int -> TreePlus -> WithEnv MetaTermPlus
reflect' level tree =
  case tree of
    (m, TreeLeaf atom)
      | level > 1 ->
        return (m, MetaTermLeaf atom)
      | Just i <- readMaybe $ T.unpack atom ->
        return (m, MetaTermInt64 i)
      | otherwise ->
        return (m, MetaTermVar $ asIdent atom)
    (m, TreeNode treeList)
      | level > 1 -> do
        case treeList of
          (_, TreeLeaf headAtom) : rest -> do
            case headAtom of
              "quote"
                | [e] <- rest -> do
                  e' <- reflect' (level + 1) e
                  return (m, MetaTermNecIntro e')
                | otherwise ->
                  raiseSyntaxError m "(quote TREE)"
              "unquote"
                | [e] <- rest -> do
                  e' <- reflect' (level - 1) e
                  return (m, MetaTermNecElim e')
                | otherwise ->
                  raiseSyntaxError m "(unquote TREE)"
              _ -> do
                treeList' <- mapM (reflect' level) treeList
                return (m, MetaTermNode treeList')
          _ -> do
            treeList' <- mapM (reflect' level) treeList
            return (m, MetaTermNode treeList')
      | otherwise ->
        case treeList of
          [] ->
            raiseSyntaxError m "(TREE TREE*)"
          leaf@(_, TreeLeaf headAtom) : rest -> do
            case headAtom of
              "lambda"
                | [(_, TreeNode xs), e] <- rest -> do
                  xs' <- mapM reflectIdent xs
                  e' <- reflect' level e
                  return (m, MetaTermImpIntro xs' e')
                | otherwise ->
                  raiseSyntaxError m "(lambda (TREE*) TREE)"
              "apply"
                | e : es <- rest -> do
                  e' <- reflect' level e
                  es' <- mapM (reflect' level) es
                  return (m, MetaTermImpElim e' es')
                | otherwise ->
                  raiseSyntaxError m "(apply TREE TREE*)"
              "quote"
                | [e] <- rest -> do
                  e' <- reflect' (level + 1) e
                  return (m, MetaTermNecIntro e')
                | otherwise ->
                  raiseSyntaxError m "(quote TREE)"
              "unquote"
                | [e] <- rest -> do
                  e' <- reflect' (level - 1) e
                  return (m, MetaTermNecElim e')
                | otherwise ->
                  raiseSyntaxError m "(unquote TREE)"
              "switch"
                | e : cs <- rest -> do
                  e' <- reflect' level e
                  cs' <- mapM (reflectEnumClause level) cs
                  return (m, MetaTermEnumElim e' cs')
                | otherwise ->
                  raiseSyntaxError m "(switch TREE TREE*)"
              _ ->
                reflectAux level m leaf rest
          leaf : rest ->
            reflectAux level m leaf rest

reflectAux :: Int -> Hint -> TreePlus -> [TreePlus] -> WithEnv MetaTermPlus
reflectAux level m f args = do
  f' <- reflect' level f
  qEnv <- gets autoQuoteEnv
  case f' of
    (_, MetaTermVar name)
      | S.member (asText name) qEnv -> do
        let args' = map wrapWithQuote args
        args'' <- mapM (reflect' level) args'
        return (m, MetaTermImpElim f' args'')
    _ -> do
      args' <- mapM (reflect' level) args
      return (m, MetaTermImpElim f' args')

reflectIdent :: TreePlus -> WithEnv Ident
reflectIdent tree =
  case tree of
    (_, TreeLeaf x) ->
      return $ asIdent x
    t ->
      raiseSyntaxError (fst t) "LEAF"

wrapWithQuote :: TreePlus -> TreePlus
wrapWithQuote (m, t) =
  (m, TreeNode [(m, TreeLeaf "quote"), (m, t)])

reflectEnumItem :: Hint -> T.Text -> [TreePlus] -> WithEnv [(T.Text, Int)]
reflectEnumItem m name ts = do
  xis <- reflectEnumItem' name $ reverse ts
  if isLinear (map snd xis)
    then return $ reverse xis
    else raiseError m "found a collision of discriminant"

reflectEnumItem' :: T.Text -> [TreePlus] -> WithEnv [(T.Text, Int)]
reflectEnumItem' name treeList =
  case treeList of
    [] ->
      return []
    [t] -> do
      (s, mj) <- reflectEnumItem'' t
      return [(name <> nsSep <> s, fromMaybe 0 mj)]
    (t : ts) -> do
      ts' <- reflectEnumItem' name ts
      (s, mj) <- reflectEnumItem'' t
      return $ (name <> nsSep <> s, fromMaybe (1 + headDiscriminantOf ts') mj) : ts'

reflectEnumItem'' :: TreePlus -> WithEnv (T.Text, Maybe Int)
reflectEnumItem'' tree =
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

reflectEnumClause :: Int -> TreePlus -> WithEnv (EnumCasePlus, MetaTermPlus)
reflectEnumClause level tree =
  case tree of
    (_, TreeNode [c, e]) -> do
      c' <- reflectEnumCase c
      e' <- reflect' level e
      return (c', e')
    e ->
      raiseSyntaxError (fst e) "(TREE TREE)"

reflectEnumCase :: TreePlus -> WithEnv EnumCasePlus
reflectEnumCase tree =
  case tree of
    (m, TreeNode [(_, TreeLeaf "enum-introduction"), (_, TreeLeaf l)]) ->
      return (m, EnumCaseLabel l)
    (m, TreeLeaf "default") ->
      return (m, EnumCaseDefault)
    (m, TreeLeaf l) ->
      return (m, EnumCaseLabel l)
    (m, _) ->
      raiseSyntaxError m "default | LEAF"
