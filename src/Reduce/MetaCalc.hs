module Reduce.MetaCalc where

import Data.Env
import Data.Ident
import qualified Data.IntMap as IntMap
import Data.MetaCalc
import Data.Tree

reduceMetaCalc :: MetaCalcPlus -> WithEnv TreePlus
reduceMetaCalc e = do
  e' <- reduceMetaCalc' e
  reifyMetaCalc e'

reduceMetaCalc' :: MetaCalcPlus -> WithEnv MetaCalcPlus
reduceMetaCalc' term =
  case term of
    (m, MetaCalcImpElim e es) -> do
      e' <- reduceMetaCalc' e
      es' <- mapM reduceMetaCalc' es
      case e' of
        (_, MetaCalcImpIntro xs body)
          | length xs == length es' -> do
            let sub = IntMap.fromList $ zip (map asInt xs) es'
            reduceMetaCalc' $ substMetaCalc sub body
        _ ->
          raiseError m "arity mismatch"
    (_, MetaCalcNecElim e) -> do
      e' <- reduceMetaCalc' e
      case e' of
        (_, MetaCalcNecIntro e'') ->
          reduceMetaCalc' e''
        (m, _) ->
          raiseError m "the inner term of an unquote must be a quoted term"
    (m, MetaCalcNode es) -> do
      es' <- mapM reduceMetaCalc' es
      return (m, MetaCalcNode es')
    _ ->
      return term

reifyMetaCalc :: MetaCalcPlus -> WithEnv TreePlus
reifyMetaCalc = undefined
