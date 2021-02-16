module Preprocess.Discern (discernMetaTerm) where

import Control.Monad.State.Lazy
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Ident
import Data.MetaTerm
import qualified Data.Text as T

type NameEnv = Map.HashMap T.Text Ident

discernMetaTerm :: MetaTermPlus -> WithEnv MetaTermPlus
discernMetaTerm e = do
  nenv <- gets topMetaNameEnv
  discernMetaTerm' nenv e

discernMetaTerm' :: NameEnv -> MetaTermPlus -> WithEnv MetaTermPlus
discernMetaTerm' nenv term =
  case term of
    (m, MetaTermVar x) ->
      case Map.lookup (asText x) nenv of
        Just x' ->
          return (m, MetaTermVar x')
        Nothing ->
          raiseError m $ "undefined variable: " <> asText x
    (m, MetaTermImpIntro xs e) -> do
      (xs', e') <- discernBinder' nenv xs e
      return (m, MetaTermImpIntro xs' e')
    (m, MetaTermImpElim e es) -> do
      e' <- discernMetaTerm' nenv e
      es' <- mapM (discernMetaTerm' nenv) es
      return (m, MetaTermImpElim e' es')
    (m, MetaTermNecIntro e) -> do
      e' <- discernMetaTerm' nenv e
      return (m, MetaTermNecIntro e')
    (m, MetaTermNecElim e) -> do
      e' <- discernMetaTerm' nenv e
      return (m, MetaTermNecElim e')
    (_, MetaTermLeaf _) ->
      return term
    (m, MetaTermNode es) -> do
      es' <- mapM (discernMetaTerm' nenv) es
      return (m, MetaTermNode es')

discernBinder' ::
  NameEnv ->
  [Ident] ->
  MetaTermPlus ->
  WithEnv ([Ident], MetaTermPlus)
discernBinder' nenv binder e =
  case binder of
    [] -> do
      e' <- discernMetaTerm' nenv e
      return ([], e')
    x : xts -> do
      x' <- newNameWith x
      (xts', e') <- discernBinder' (Map.insert (asText x) x' nenv) xts e
      return (x' : xts', e')
