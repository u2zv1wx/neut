module Preprocess.Interpret
  ( interpretMetaTerm,
  )
where

import Data.Env
import Data.Hint
import Data.Ident
import Data.MetaTerm
import Data.Tree

interpretMetaTerm :: TreePlus -> WithEnv MetaTermPlus
interpretMetaTerm tree =
  interpretMetaTerm' 0 tree

interpretMetaTerm' :: Int -> TreePlus -> WithEnv MetaTermPlus
interpretMetaTerm' level tree =
  case tree of
    (m, TreeLeaf atom)
      | level == 0 ->
        return (m, MetaTermLeaf atom)
      | otherwise ->
        return (m, MetaTermVar $ asIdent atom)
    (m, TreeNode (leaf@(_, TreeLeaf headAtom) : rest)) ->
      case headAtom of
        "LAMBDA"
          | [(_, TreeNode xs), e] <- rest -> do
            if level <= 0
              then raiseError m "a meta-abstraction can only be used in the meta language"
              else do
                xs' <- mapM interpretIdent xs
                e' <- interpretMetaTerm' level e
                return (m, MetaTermImpIntro xs' e')
          | otherwise ->
            raiseSyntaxError m "(LAMBDA (TREE*) TREE)"
        "APPLY"
          | e : es <- rest -> do
            if level <= 0
              then raiseError m "a meta-application can only be used in the meta language"
              else do
                e' <- interpretMetaTerm' level e
                es' <- mapM (interpretMetaTerm' level) es
                return (m, MetaTermImpElim e' es')
          | otherwise ->
            raiseSyntaxError m "(APPLY TREE TREE*)"
        "QUOTE"
          | [e] <- rest -> do
            if level <= 0
              then raiseError m "a quotation can only be used in the meta language"
              else do
                e' <- interpretMetaTerm' (level - 1) e
                return (m, MetaTermNecIntro e')
          | otherwise ->
            raiseSyntaxError m "(necessity-introduction TREE)"
        "UNQUOTE"
          | [e] <- rest -> do
            e' <- interpretMetaTerm' (level + 1) e
            return (m, MetaTermNecElim e')
          | otherwise ->
            raiseSyntaxError m "(UNQUOTE TREE)"
        _ ->
          interpretMetaTermAux level m $ leaf : rest
    (m, TreeNode es) ->
      interpretMetaTermAux level m es

interpretMetaTermAux :: Int -> Hint -> [TreePlus] -> WithEnv MetaTermPlus
interpretMetaTermAux level m es = do
  es' <- mapM (interpretMetaTerm' level) es
  if level == 0
    then return (m, MetaTermNode es')
    else case es of
      [] ->
        raiseSyntaxError m "(TREE TREE*)"
      f : args -> do
        f' <- interpretMetaTerm' level f
        args' <- mapM (interpretMetaTerm' level) args
        return (m, MetaTermImpElim f' args')

interpretIdent :: TreePlus -> WithEnv Ident
interpretIdent tree =
  case tree of
    (_, TreeLeaf x) ->
      return $ asIdent x
    t ->
      raiseSyntaxError (fst t) "LEAF"
