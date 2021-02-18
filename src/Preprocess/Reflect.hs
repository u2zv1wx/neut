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
import Text.Read (readMaybe)

reflect :: MetaTermPlus -> WithEnv MetaTermPlus
reflect tree =
  reflect' 1 tree

reflect' :: Int -> MetaTermPlus -> WithEnv MetaTermPlus
reflect' level tree =
  case tree of
    (m, MetaTermLeaf atom)
      | level > 1 ->
        return (m, MetaTermLeaf atom)
      | Just i <- readMaybe $ T.unpack atom ->
        return (m, MetaTermInt64 i)
      | otherwise ->
        return (m, MetaTermVar $ asIdent atom)
    (m, MetaTermNode treeList)
      | level > 1 -> do
        case treeList of
          (_, MetaTermLeaf headAtom) : rest -> do
            case headAtom of
              "leaf"
                | [(_, MetaTermLeaf atom)] <- rest -> do
                  return (m, MetaTermLeaf atom)
                | otherwise ->
                  raiseSyntaxError m "(leaf LEAF)"
              "node" -> do
                rest' <- mapM (reflect' level) rest
                return (m, MetaTermNode rest')
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
          leaf@(_, MetaTermLeaf headAtom) : rest -> do
            case headAtom of
              "lambda"
                | [(_, MetaTermNode xs), e] <- rest -> do
                  xs' <- mapM reflectIdent xs
                  e' <- reflect' level e
                  return (m, MetaTermImpIntro xs' Nothing e')
                | otherwise ->
                  raiseSyntaxError m "(lambda (LEAF*) TREE)"
              "lambda+"
                | [(_, MetaTermNode args@(_ : _)), e] <- rest -> do
                  xs' <- mapM reflectIdent (init args)
                  rest' <- reflectIdent $ last args
                  e' <- reflect' level e
                  return (m, MetaTermImpIntro xs' (Just rest') e')
                | otherwise ->
                  raiseSyntaxError m "(lambda+ (LEAF LEAF*) TREE)"
              "apply"
                | e : es <- rest -> do
                  e' <- reflect' level e
                  es' <- mapM (reflect' level) es
                  return (m, MetaTermImpElim e' es')
                | otherwise ->
                  raiseSyntaxError m "(apply TREE TREE*)"
              "fix"
                | [(_, MetaTermLeaf f), (_, MetaTermNode xs), e] <- rest -> do
                  xs' <- mapM reflectIdent xs
                  e' <- reflect e
                  return (m, MetaTermFix (asIdent f) xs' Nothing e')
                | otherwise ->
                  raiseSyntaxError m "(fix LEAF (LEAF*) TREE)"
              "fix+"
                | [(_, MetaTermLeaf f), (_, MetaTermNode args@(_ : _)), e] <- rest -> do
                  xs' <- mapM reflectIdent (init args)
                  rest' <- reflectIdent $ last args
                  e' <- reflect e
                  return (m, MetaTermFix (asIdent f) xs' (Just rest') e')
                | otherwise ->
                  raiseSyntaxError m "(fix+ LEAF (LEAF LEAF*) TREE)"
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
              "thunk"
                | [e] <- rest -> do
                  e' <- reflect' level e
                  return (m, MetaTermImpIntro [] Nothing e')
                | otherwise ->
                  raiseSyntaxError m "(thunk TREE)"
              _ ->
                reflectAux level m leaf rest
          leaf : rest ->
            reflectAux level m leaf rest
    (m, MetaTermNecIntro e) -> do
      e' <- reflect' (level + 1) e
      return (m, MetaTermNecIntro e')
    (m, MetaTermNecElim e) -> do
      e' <- reflect' (level - 1) e
      return (m, MetaTermNecElim e')
    (m, _) -> do
      raiseCritical m "Preprocess.Reflect.reflect called for a non-AST term (compiler bug)"

reflectAux :: Int -> Hint -> MetaTermPlus -> [MetaTermPlus] -> WithEnv MetaTermPlus
reflectAux level m f args = do
  f' <- reflect' level f
  args' <- modifyArgs f args
  args'' <- mapM (reflect' level) args'
  return (m, MetaTermImpElim f' args'')

modifyArgs :: MetaTermPlus -> [MetaTermPlus] -> WithEnv [MetaTermPlus]
modifyArgs f args = do
  thunkEnv <- gets autoThunkEnv
  quoteEnv <- gets autoQuoteEnv
  case f of
    (_, MetaTermVar name)
      | S.member (asText name) thunkEnv ->
        return $ map wrapWithThunk args
      | S.member (asText name) quoteEnv ->
        return $ map wrapWithQuote args
    _ ->
      return args

reflectIdent :: MetaTermPlus -> WithEnv Ident
reflectIdent tree =
  case tree of
    (_, MetaTermLeaf x) ->
      return $ asIdent x
    t ->
      raiseSyntaxError (fst t) "LEAF"

wrapWithThunk :: MetaTermPlus -> MetaTermPlus
wrapWithThunk (m, t) =
  (m, MetaTermNode [(m, MetaTermLeaf "thunk"), (m, t)])

wrapWithQuote :: MetaTermPlus -> MetaTermPlus
wrapWithQuote (m, t) =
  (m, MetaTermNode [(m, MetaTermLeaf "quote"), (m, t)])

reflectEnumItem :: Hint -> T.Text -> [MetaTermPlus] -> WithEnv [(T.Text, Int)]
reflectEnumItem m name ts = do
  xis <- reflectEnumItem' name $ reverse ts
  if isLinear (map snd xis)
    then return $ reverse xis
    else raiseError m "found a collision of discriminant"

reflectEnumItem' :: T.Text -> [MetaTermPlus] -> WithEnv [(T.Text, Int)]
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

reflectEnumItem'' :: MetaTermPlus -> WithEnv (T.Text, Maybe Int)
reflectEnumItem'' tree =
  case tree of
    (_, MetaTermLeaf s) ->
      return (s, Nothing)
    (_, MetaTermNode [(_, MetaTermLeaf s), (_, MetaTermLeaf i)])
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

reflectEnumClause :: Int -> MetaTermPlus -> WithEnv (EnumCasePlus, MetaTermPlus)
reflectEnumClause level tree =
  case tree of
    (_, MetaTermNode [c, e]) -> do
      c' <- reflectEnumCase c
      e' <- reflect' level e
      return (c', e')
    e ->
      raiseSyntaxError (fst e) "(TREE TREE)"

reflectEnumCase :: MetaTermPlus -> WithEnv EnumCasePlus
reflectEnumCase tree =
  case tree of
    (m, MetaTermNode [(_, MetaTermLeaf "enum-introduction"), (_, MetaTermLeaf l)]) ->
      return (m, EnumCaseLabel l)
    (m, MetaTermLeaf "default") ->
      return (m, EnumCaseDefault)
    (m, MetaTermLeaf l) ->
      return (m, EnumCaseLabel l)
    (m, _) ->
      raiseSyntaxError m "default | LEAF"
