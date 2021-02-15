module Reduce.MetaCalc where

import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.MetaCalc

reduceMetaCalc :: MetaCalcPlus -> WithEnv MetaCalcPlus
reduceMetaCalc term =
  case term of
    (m, MetaCalcArrowElim e es) -> do
      e' <- reduceMetaCalc e
      es' <- mapM reduceMetaCalc es
      case e' of
        (_, MetaCalcArrowIntro xs body)
          | length xs == length es' -> do
            let sub = Map.fromList $ zip xs es'
            reduceMetaCalc $ substMetaCalc sub body
        _ ->
          raiseError m "arity mismatch"
    (_, MetaCalcBoxElim e) -> do
      e' <- reduceMetaCalc e
      case e' of
        (_, MetaCalcBoxIntro e'') ->
          reduceMetaCalc e''
        (m, _) ->
          raiseError m "the inner term of an unquote must be a quoted term"
    (m, MetaCalcNode es) -> do
      es' <- mapM reduceMetaCalc es
      return (m, MetaCalcNode es')
    _ ->
      return term
