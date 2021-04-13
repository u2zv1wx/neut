module Preprocess.Discern
  ( discernMetaTerm,
  )
where

import Data.Basic
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.IORef
import Data.Log
import Data.MetaTerm
import Data.Namespace
import qualified Data.Text as T

type NameEnv = Map.HashMap T.Text Ident

discernMetaTerm :: MetaTermPlus -> IO MetaTermPlus
discernMetaTerm e = do
  nenv <- readIORef topMetaNameEnv
  discernMetaTerm' nenv e

discernMetaTerm' :: NameEnv -> MetaTermPlus -> IO MetaTermPlus
discernMetaTerm' nenv term =
  case term of
    (m, MetaTermVar (I (s, _))) ->
      tryCand (resolveSymbol m (asMetaVar m nenv) s) $
        tryCand (resolveSymbol m (asMetaConstant m) s) $
          raiseError m $ "undefined meta-variable: " <> s
    (m, MetaTermImpIntro mf xs mx e) -> do
      case mf of
        Nothing -> do
          (xs', mx', e') <- discernBinder nenv xs mx e
          return (m, MetaTermImpIntro Nothing xs' mx' e')
        Just f -> do
          (f' : xs', mx', e') <- discernBinder nenv (f : xs) mx e
          return (m, MetaTermImpIntro (Just f') xs' mx' e')
    (m, MetaTermImpElim e es) -> do
      e' <- discernMetaTerm' nenv e
      es' <- mapM (discernMetaTerm' nenv) es
      return (m, MetaTermImpElim e' es')
    (_, MetaTermLeaf _) ->
      return term
    (m, MetaTermNode es) -> do
      es' <- mapM (discernMetaTerm' nenv) es
      return (m, MetaTermNode es')
    (_, MetaTermConst _) ->
      return term
    (_, MetaTermInteger _) ->
      return term
    (m, MetaTermIf cond onTrue onFalse) -> do
      cond' <- discernMetaTerm' nenv cond
      onTrue' <- discernMetaTerm' nenv onTrue
      onFalse' <- discernMetaTerm' nenv onFalse
      return (m, MetaTermIf cond' onTrue' onFalse')

discernBinder ::
  NameEnv ->
  [Ident] ->
  Maybe Ident ->
  MetaTermPlus ->
  IO ([Ident], Maybe Ident, MetaTermPlus)
discernBinder nenv binder mf e =
  case binder of
    [] -> do
      case mf of
        Just f -> do
          f' <- newIdentFromIdent f
          e' <- discernMetaTerm' (Map.insert (asText f) f' nenv) e
          return ([], Just f', e')
        Nothing -> do
          e' <- discernMetaTerm' nenv e
          return ([], Nothing, e')
    x : xs -> do
      x' <- newIdentFromIdent x
      (xs', mf', e') <- discernBinder (Map.insert (asText x) x' nenv) xs mf e
      return (x' : xs', mf', e')
