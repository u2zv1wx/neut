module Preprocess.Interpret
  ( interpretCode,
  )
where

import Data.Basic
import Data.Env
import Data.Log
import Data.MetaTerm
import qualified Data.Text as T
import Data.Tree
import Text.Read (readMaybe)

interpretCode :: TreePlus -> WithEnv MetaTermPlus
interpretCode tree =
  case tree of
    (m, TreeLeaf atom)
      | Just i <- readMaybe $ T.unpack atom ->
        return (m, MetaTermInteger i)
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
            "if-meta"
              | [cond, onTrue, onFalse] <- rest -> do
                cond' <- interpretCode cond
                onTrue' <- interpretCode onTrue
                onFalse' <- interpretCode onFalse
                return (m, MetaTermIf cond' onTrue' onFalse')
              | otherwise ->
                raiseSyntaxError m "(if-meta TREE TREE TREE)"
            "leaf"
              | [(_, TreeLeaf x)] <- rest -> do
                return (m, MetaTermLeaf x)
              | [] <- rest -> do
                return (m, MetaTermLeaf "") -- the unit element of the free monoid
              | otherwise ->
                raiseSyntaxError m "(leaf TREE)"
            "node" -> do
              rest' <- mapM interpretCode rest
              return (m, MetaTermNode rest')
            "quote"
              | [e] <- rest -> do
                interpretData e
              | otherwise ->
                raiseSyntaxError m "(quote TREE)"
            "unquote"
              | [_] <- rest ->
                raiseError m "found an unquote when parsing given AST as code"
              | otherwise ->
                raiseSyntaxError m "(unquote TREE)"
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

interpretData :: TreePlus -> WithEnv MetaTermPlus
interpretData tree = do
  case tree of
    (m, TreeLeaf atom) ->
      return (m, MetaTermLeaf atom)
    (m, TreeNode treeList) ->
      case treeList of
        (_, TreeLeaf "quote") : rest
          | [_] <- rest ->
            raiseError m "found a quote when parsing given AST as data"
          | otherwise ->
            raiseSyntaxError m "(quote TREE)"
        (_, TreeLeaf "unquote") : rest
          | [e] <- rest -> do
            interpretCode e
          | otherwise ->
            raiseSyntaxError m "(unquote TREE)"
        _
          | containsSpliceArg treeList -> do
            args <- interpretSpliceArg treeList
            return (m, MetaTermImpElim (m, MetaTermVar $ asIdent "meta.node.list") args)
          | otherwise -> do
            treeList' <- mapM interpretData treeList
            return (m, MetaTermNode treeList')

containsSpliceArg :: [TreePlus] -> Bool
containsSpliceArg ts =
  case ts of
    [] ->
      False
    (_, TreeNode [(_, TreeLeaf "splice"), _]) : _ ->
      True
    _ : rest ->
      containsSpliceArg rest

interpretSpliceArg :: [TreePlus] -> WithEnv [MetaTermPlus]
interpretSpliceArg ts =
  case ts of
    [] ->
      return []
    (_, TreeNode [(_, TreeLeaf "splice"), t]) : rest -> do
      t' <- interpretData t
      rest' <- interpretSpliceArg rest
      return $ t' : rest'
    t : rest -> do
      t' <- interpretData t
      rest' <- interpretSpliceArg rest
      return $ (fst t', MetaTermNode [t']) : rest'

interpretAux :: Hint -> TreePlus -> [TreePlus] -> WithEnv MetaTermPlus
interpretAux m f args = do
  f' <- interpretCode f
  (xts, args') <- interpretArg args
  if null xts
    then return (m, MetaTermImpElim f' args')
    else return (m, MetaTermImpIntro xts Nothing (m, MetaTermImpElim f' args'))

interpretArg :: [TreePlus] -> WithEnv ([Ident], [MetaTermPlus])
interpretArg es =
  case es of
    [] ->
      return ([], [])
    tree : treeList -> do
      (xts, args) <- interpretArg treeList
      case tree of
        (m, TreeLeaf "_") -> do
          h <- interpretIdent tree
          return (h : xts, (m, MetaTermVar h) : args)
        _ -> do
          e <- interpretCode tree
          return (xts, e : args)

interpretIdent :: TreePlus -> WithEnv Ident
interpretIdent tree = do
  x' <- interpretLeafText tree
  return $ asIdent x'

interpretLeafText :: TreePlus -> WithEnv T.Text
interpretLeafText tree =
  case tree of
    (_, TreeLeaf "_") -> do
      h <- newText
      return h
    (_, TreeLeaf x) ->
      return x
    t ->
      raiseSyntaxError (fst t) "LEAF"

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
