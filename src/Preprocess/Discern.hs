module Preprocess.Discern
  ( discernMetaTerm,
    discernEnumCase,
  )
where

import Control.Monad.State.Lazy
import Data.Basic
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Log
import Data.MetaTerm
import Data.Namespace
import qualified Data.Text as T

type NameEnv = Map.HashMap T.Text Ident

discernMetaTerm :: MetaTermPlus -> WithEnv MetaTermPlus
discernMetaTerm e = do
  nenv <- gets topMetaNameEnv
  discernMetaTerm' nenv e

discernMetaTerm' :: NameEnv -> MetaTermPlus -> WithEnv MetaTermPlus
discernMetaTerm' nenv term =
  case term of
    (m, MetaTermVar (I (s, _))) ->
      tryCand (resolveSymbol (asMetaVar m nenv) s) $
        tryCand (resolveSymbol (asMetaEnumValue m) s) $
          tryCand (resolveSymbol (asMetaConstant m) s) $
            raiseError m $ "undefined meta-variable: " <> s
    (m, MetaTermImpIntro xs mf e) -> do
      (xs', mf', e') <- discernBinder nenv xs mf e
      return (m, MetaTermImpIntro xs' mf' e')
    (m, MetaTermImpElim e es) -> do
      e' <- discernMetaTerm' nenv e
      es' <- mapM (discernMetaTerm' nenv) es
      return (m, MetaTermImpElim e' es')
    (m, MetaTermFix f xs mx e) -> do
      (f' : xs', mx', e') <- discernBinder nenv (f : xs) mx e
      return (m, MetaTermFix f' xs' mx' e')
    (_, MetaTermLeaf _) ->
      return term
    (m, MetaTermNode es) -> do
      es' <- mapM (discernMetaTerm' nenv) es
      return (m, MetaTermNode es')
    (_, MetaTermConst _) ->
      return term
    (_, MetaTermInt64 _) ->
      return term
    (_, MetaTermEnumIntro _) ->
      return term
    (m, MetaTermEnumElim (e, i) caseList) -> do
      e' <- discernMetaTerm' nenv e
      caseList' <-
        forM caseList $ \((mCase, l), body) -> do
          l' <- discernEnumCase mCase l
          body' <- discernMetaTerm' nenv body
          return ((mCase, l'), body')
      return (m, MetaTermEnumElim (e', i) caseList')

discernBinder ::
  NameEnv ->
  [Ident] ->
  Maybe Ident ->
  MetaTermPlus ->
  WithEnv ([Ident], Maybe Ident, MetaTermPlus)
discernBinder nenv binder mf e =
  case binder of
    [] -> do
      case mf of
        Just f -> do
          f' <- newNameWith f
          e' <- discernMetaTerm' (Map.insert (asText f) f' nenv) e
          return ([], Just f', e')
        Nothing -> do
          e' <- discernMetaTerm' nenv e
          return ([], Nothing, e')
    x : xs -> do
      x' <- newNameWith x
      (xs', mf', e') <- discernBinder (Map.insert (asText x) x' nenv) xs mf e
      return (x' : xs', mf', e')

discernEnumCase :: Hint -> EnumCase -> WithEnv EnumCase
discernEnumCase m weakCase =
  case weakCase of
    EnumCaseLabel l -> do
      ml <- resolveSymbol asEnumCase l
      case ml of
        Just l' ->
          return l'
        Nothing -> do
          e <- gets enumEnv
          p' e
          raiseError m $ "no such enum-value is defined: " <> l
    _ ->
      return weakCase
