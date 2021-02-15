module Preprocess.Interpret
  ( raiseSyntaxError,
    interpretMetaCalc,
  )
where

import Data.Env
import Data.Hint
import Data.Ident
import Data.MetaCalc
import Data.Tree

interpretMetaCalc :: TreePlus -> WithEnv MetaCalcPlus
interpretMetaCalc tree =
  case tree of
    (m, TreeLeaf atom) ->
      return (m, MetaCalcVar $ asIdent atom)
    (m, TreeNode (leaf@(_, TreeLeaf headAtom) : rest)) ->
      case headAtom of
        "implication-introduction"
          | [(_, TreeNode xs), e] <- rest -> do
            xs' <- mapM interpretIdent xs
            e' <- interpretMetaCalc e
            return (m, MetaCalcImpIntro xs' e')
          | otherwise ->
            raiseSyntaxError m "(implication-introduction (TREE*) TREE)"
        "implication-elimination"
          | e : es <- rest -> do
            e' <- interpretMetaCalc e
            es' <- mapM interpretMetaCalc es
            return (m, MetaCalcImpElim e' es')
          | otherwise ->
            raiseSyntaxError m "(implication-elimination TREE TREE*)"
        "necessity-introduction"
          | [e] <- rest -> do
            e' <- interpretMetaCalc e
            return (m, MetaCalcNecIntro e')
          | otherwise ->
            raiseSyntaxError m "(necessity-introduction TREE)"
        "necessity-elimination"
          | [e] <- rest -> do
            e' <- interpretMetaCalc e
            return (m, MetaCalcNecElim e')
          | otherwise ->
            raiseSyntaxError m "(necessity-elimination TREE)"
        _ ->
          interpretMetaCalcAux m $ leaf : rest
    (m, TreeNode es) ->
      interpretMetaCalcAux m es

interpretMetaCalcAux :: Hint -> [TreePlus] -> WithEnv MetaCalcPlus
interpretMetaCalcAux m es = do
  es' <- mapM interpretMetaCalc es
  return (m, MetaCalcNode es')

interpretIdent :: TreePlus -> WithEnv Ident
interpretIdent tree =
  case tree of
    (_, TreeLeaf x) ->
      return $ asIdent x
    t ->
      raiseSyntaxError (fst t) "LEAF"
