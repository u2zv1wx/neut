module Preprocess.Discern (discernMetaCalc) where

import Control.Monad.State.Lazy
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Ident
import Data.MetaCalc
import qualified Data.Text as T

type NameEnv = Map.HashMap T.Text Ident

discernMetaCalc :: MetaCalcPlus -> WithEnv MetaCalcPlus
discernMetaCalc e = do
  nenv <- gets topMetaNameEnv
  discernMetaCalc' nenv e

discernMetaCalc' :: NameEnv -> MetaCalcPlus -> WithEnv MetaCalcPlus
discernMetaCalc' nenv term =
  case term of
    (m, MetaCalcVar x) -> do
      let mx = Map.lookup (asText x) nenv
      case mx of
        Just x' ->
          return (m, MetaCalcVar x')
        Nothing ->
          return (m, MetaCalcLeaf (asText x))
    (m, MetaCalcImpIntro xs e) -> do
      (xs', e') <- discernBinder' nenv xs e
      return (m, MetaCalcImpIntro xs' e')
    (m, MetaCalcImpElim e es) -> do
      e' <- discernMetaCalc' nenv e
      es' <- mapM (discernMetaCalc' nenv) es
      return (m, MetaCalcImpElim e' es')
    (m, MetaCalcNecIntro e) -> do
      e' <- discernMetaCalc' nenv e
      return (m, MetaCalcNecIntro e')
    (m, MetaCalcNecElim e) -> do
      e' <- discernMetaCalc' nenv e
      return (m, MetaCalcNecElim e')
    (_, MetaCalcLeaf _) ->
      return term
    (m, MetaCalcNode es) -> do
      es' <- mapM (discernMetaCalc' nenv) es
      case es' of
        e@(_, MetaCalcVar _) : rest
          | True ->
            return (m, MetaCalcImpElim e rest)
        _ ->
          return (m, MetaCalcNode es')

discernBinder' ::
  NameEnv ->
  [Ident] ->
  MetaCalcPlus ->
  WithEnv ([Ident], MetaCalcPlus)
discernBinder' nenv binder e =
  case binder of
    [] -> do
      e' <- discernMetaCalc' nenv e
      return ([], e')
    x : xts -> do
      x' <- newNameWith x
      (xts', e') <- discernBinder' (insertName x x' nenv) xts e
      return (x' : xts', e')

insertName :: Ident -> Ident -> NameEnv -> NameEnv
insertName (I (s, _)) =
  Map.insert s
