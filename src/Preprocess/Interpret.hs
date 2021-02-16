module Preprocess.Interpret
  ( raiseSyntaxError,
    interpretMetaTerm,
  )
where

import Data.Env
import Data.Hint
import Data.Ident
import Data.MetaTerm
import Data.Tree

interpretMetaTerm :: TreePlus -> WithEnv MetaTermPlus
interpretMetaTerm tree =
  case tree of
    (m, TreeLeaf atom) ->
      return (m, MetaTermVar $ asIdent atom)
    (m, TreeNode (leaf@(_, TreeLeaf headAtom) : rest)) ->
      case headAtom of
        "implication-introduction"
          | [(_, TreeNode xs), e] <- rest -> do
            xs' <- mapM interpretIdent xs
            e' <- interpretMetaTerm e
            return (m, MetaTermImpIntro xs' e')
          | otherwise ->
            raiseSyntaxError m "(implication-introduction (TREE*) TREE)"
        "implication-elimination"
          | e : es <- rest -> do
            e' <- interpretMetaTerm e
            es' <- mapM interpretMetaTerm es
            return (m, MetaTermImpElim e' es')
          | otherwise ->
            raiseSyntaxError m "(implication-elimination TREE TREE*)"
        "necessity-introduction"
          | [e] <- rest -> do
            e' <- interpretMetaTerm e
            return (m, MetaTermNecIntro e')
          | otherwise ->
            raiseSyntaxError m "(necessity-introduction TREE)"
        "necessity-elimination"
          | [e] <- rest -> do
            e' <- interpretMetaTerm e
            return (m, MetaTermNecElim e')
          | otherwise ->
            raiseSyntaxError m "(necessity-elimination TREE)"
        _ ->
          interpretMetaTermAux m $ leaf : rest
    (m, TreeNode es) ->
      interpretMetaTermAux m es

interpretMetaTermAux :: Hint -> [TreePlus] -> WithEnv MetaTermPlus
interpretMetaTermAux m es = do
  es' <- mapM interpretMetaTerm es
  return (m, MetaTermNode es')

interpretIdent :: TreePlus -> WithEnv Ident
interpretIdent tree =
  case tree of
    (_, TreeLeaf x) ->
      return $ asIdent x
    t ->
      raiseSyntaxError (fst t) "LEAF"
