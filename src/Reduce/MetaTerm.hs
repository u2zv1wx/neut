module Reduce.MetaTerm where

import Data.Env
import Data.Ident
import qualified Data.IntMap as IntMap
import Data.MetaTerm
import Data.Tree

reduceMetaTerm :: MetaTermPlus -> WithEnv TreePlus
reduceMetaTerm e = do
  e' <- reduceMetaTerm' e
  reifyMetaTerm e'

reduceMetaTerm' :: MetaTermPlus -> WithEnv MetaTermPlus
reduceMetaTerm' term =
  case term of
    (m, MetaTermImpElim e es) -> do
      e' <- reduceMetaTerm' e
      es' <- mapM reduceMetaTerm' es
      case e' of
        (_, MetaTermImpIntro xs body)
          | length xs == length es' -> do
            let sub = IntMap.fromList $ zip (map asInt xs) es'
            reduceMetaTerm' $ substMetaTerm sub body
        _ ->
          raiseError m "arity mismatch"
    (_, MetaTermNecElim e) -> do
      e' <- reduceMetaTerm' e
      case e' of
        (_, MetaTermNecIntro e'') ->
          reduceMetaTerm' e''
        (m, _) ->
          raiseError m "the inner term of an unquote must be a quoted term"
    (m, MetaTermNode es) -> do
      es' <- mapM reduceMetaTerm' es
      return (m, MetaTermNode es')
    _ ->
      return term

reifyMetaTerm :: MetaTermPlus -> WithEnv TreePlus
reifyMetaTerm = undefined
