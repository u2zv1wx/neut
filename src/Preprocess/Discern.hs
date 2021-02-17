module Preprocess.Discern (discernMetaTerm, discernEnumCase) where

import Control.Monad.State.Lazy
import Data.EnumCase
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Hint
import Data.Ident
import Data.MetaTerm
import qualified Data.Set as S
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
        Nothing -> do
          cenv <- gets metaConstantSet
          if S.member (asText x) cenv
            then return (m, MetaTermConst (asText x))
            else do
              mEnumValue <- resolveAsEnumValue (asText x)
              case mEnumValue of
                Just enumValue ->
                  return (m, MetaTermEnumIntro enumValue)
                Nothing ->
                  raiseError m $ "undefined variable: " <> asText x
    (m, MetaTermImpIntro xs e) -> do
      (xs', e') <- discernBinder' nenv xs e
      return (m, MetaTermImpIntro xs' e')
    (m, MetaTermImpElim e es) -> do
      e' <- discernMetaTerm' nenv e
      es' <- mapM (discernMetaTerm' nenv) es
      return (m, MetaTermImpElim e' es')
    (m, MetaTermFix f xs e) -> do
      (f' : xs', e') <- discernBinder' nenv (f : xs) e
      return (m, MetaTermFix f' xs' e')
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
    (_, MetaTermConst _) ->
      return term
    (_, MetaTermInt64 _) ->
      return term
    (_, MetaTermEnumIntro _) ->
      return term
    (m, MetaTermEnumElim e caseList) -> do
      e' <- discernMetaTerm' nenv e
      caseList' <-
        forM caseList $ \((mCase, l), body) -> do
          l' <- discernEnumCase mCase l
          body' <- discernMetaTerm' nenv body
          return ((mCase, l'), body')
      return (m, MetaTermEnumElim e' caseList')

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

discernEnumCase :: Hint -> EnumCase -> WithEnv EnumCase
discernEnumCase m weakCase =
  case weakCase of
    EnumCaseLabel l -> do
      ml <- resolveAsEnumValue l
      case ml of
        Just l' ->
          return (EnumCaseLabel l')
        Nothing ->
          raiseError m $ "no such enum-value is defined: " <> l
    _ ->
      return weakCase
