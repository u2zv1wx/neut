module Preprocess.Reflect
  ( reflect,
  )
where

import Data.Env
import Data.Hint
import Data.Ident
import Data.MetaTerm
import Data.Tree

reflect :: TreePlus -> WithEnv MetaTermPlus
reflect tree =
  reflect' 1 tree

reflect' :: Int -> TreePlus -> WithEnv MetaTermPlus
reflect' level tree =
  case tree of
    (m, TreeLeaf atom)
      | level > 1 ->
        return (m, MetaTermLeaf atom)
      | otherwise ->
        return (m, MetaTermVar $ asIdent atom)
    (m, TreeNode treeList)
      | level > 1 -> do
        case treeList of
          (_, TreeLeaf headAtom) : rest -> do
            case headAtom of
              "QUOTE"
                | [e] <- rest -> do
                  e' <- reflect' (level + 1) e
                  return (m, MetaTermNecIntro e')
                | otherwise ->
                  raiseSyntaxError m "(QUOTE TREE)"
              "UNQUOTE"
                | [e] <- rest -> do
                  e' <- reflect' (level - 1) e
                  return (m, MetaTermNecElim e')
                | otherwise ->
                  raiseSyntaxError m "(UNQUOTE TREE)"
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
              "LAMBDA"
                | [(_, TreeNode xs), e] <- rest -> do
                  xs' <- mapM reflectIdent xs
                  e' <- reflect' level e
                  return (m, MetaTermImpIntro xs' e')
                | otherwise ->
                  raiseSyntaxError m "(LAMBDA (TREE*) TREE)"
              "APPLY"
                | e : es <- rest -> do
                  e' <- reflect' level e
                  es' <- mapM (reflect' level) es
                  return (m, MetaTermImpElim e' es')
                | otherwise ->
                  raiseSyntaxError m "(APPLY TREE TREE*)"
              "QUOTE"
                | [e] <- rest -> do
                  e' <- reflect' (level + 1) e
                  return (m, MetaTermNecIntro e')
                | otherwise ->
                  raiseSyntaxError m "(QUOTE TREE)"
              "UNQUOTE"
                | [e] <- rest -> do
                  e' <- reflect' (level - 1) e
                  return (m, MetaTermNecElim e')
                | otherwise ->
                  raiseSyntaxError m "(UNQUOTE TREE)"
              _ ->
                reflectAux level m leaf rest
          leaf : rest ->
            reflectAux level m leaf rest

reflectAux :: Int -> Hint -> TreePlus -> [TreePlus] -> WithEnv MetaTermPlus
reflectAux level m f args = do
  f' <- reflect' level f
  args' <- mapM (reflect' level) args
  return (m, MetaTermImpElim f' args')

reflectIdent :: TreePlus -> WithEnv Ident
reflectIdent tree =
  case tree of
    (_, TreeLeaf x) ->
      return $ asIdent x
    t ->
      raiseSyntaxError (fst t) "LEAF"
