module Preprocess.Discern
  ( discernMetaTerm,
    discernEnumCase,
    discernMetaType,
  )
where

import Control.Monad.State.Lazy
import Data.EnumCase
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Hint
import Data.Ident
import Data.MetaTerm
import qualified Data.Set as S
import qualified Data.Text as T

type NameEnv = Map.HashMap (T.Text, Level) Ident

discernMetaTerm :: MetaTermPlus -> WithEnv MetaTermPlus
discernMetaTerm e = do
  nenv <- gets topMetaNameEnv
  discernMetaTerm' 1 nenv e

discernMetaTerm' :: Int -> NameEnv -> MetaTermPlus -> WithEnv MetaTermPlus
discernMetaTerm' levelOfJudgement nenv term =
  case term of
    (m, MetaTermVar x) ->
      case Map.lookup (asText x, LevelMono levelOfJudgement) nenv of
        Just x' ->
          return (m, MetaTermVar x')
        _ ->
          case Map.lookup (asText x, LevelPoly) nenv of
            Just x' ->
              return (m, MetaTermVar x')
            _ -> do
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
    (m, MetaTermImpIntro xs mf e) -> do
      (xs', mf', e') <- discernBinder levelOfJudgement nenv xs mf e
      return (m, MetaTermImpIntro xs' mf' e')
    (m, MetaTermImpElim e es) -> do
      e' <- discernMetaTerm' levelOfJudgement nenv e
      es' <- mapM (discernMetaTerm' levelOfJudgement nenv) es
      return (m, MetaTermImpElim e' es')
    (m, MetaTermFix f xs mx e) -> do
      (f' : xs', mx', e') <- discernBinder levelOfJudgement nenv (f : xs) mx e
      return (m, MetaTermFix f' xs' mx' e')
    (m, MetaTermNecIntro e) -> do
      e' <- discernMetaTerm' (levelOfJudgement + 1) nenv e
      return (m, MetaTermNecIntro e')
    (m, MetaTermNecElim e) -> do
      e' <- discernMetaTerm' (levelOfJudgement - 1) nenv e
      return (m, MetaTermNecElim e')
    (_, MetaTermLeaf _) ->
      return term
    (m, MetaTermNode es) -> do
      es' <- mapM (discernMetaTerm' levelOfJudgement nenv) es
      return (m, MetaTermNode es')
    (_, MetaTermConst _) ->
      return term
    (_, MetaTermInt64 _) ->
      return term
    (_, MetaTermEnumIntro _) ->
      return term
    (m, MetaTermEnumElim (e, i) caseList) -> do
      e' <- discernMetaTerm' levelOfJudgement nenv e
      caseList' <-
        forM caseList $ \((mCase, l), body) -> do
          l' <- discernEnumCase mCase l
          body' <- discernMetaTerm' levelOfJudgement nenv body
          return ((mCase, l'), body')
      return (m, MetaTermEnumElim (e', i) caseList')

discernBinder ::
  Int ->
  NameEnv ->
  [Ident] ->
  Maybe Ident ->
  MetaTermPlus ->
  WithEnv ([Ident], Maybe Ident, MetaTermPlus)
discernBinder levelOfJudgement nenv binder mf e =
  case binder of
    [] -> do
      case mf of
        Just f -> do
          f' <- newNameWith f
          e' <- discernMetaTerm' levelOfJudgement (Map.insert (asText f, LevelMono levelOfJudgement) f' nenv) e
          return ([], Just f', e')
        Nothing -> do
          e' <- discernMetaTerm' levelOfJudgement nenv e
          return ([], Nothing, e')
    x : xs -> do
      x' <- newNameWith x
      (xs', mf', e') <- discernBinder levelOfJudgement (Map.insert (asText x, LevelMono levelOfJudgement) x' nenv) xs mf e
      return (x' : xs', mf', e')

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

discernMetaType :: [Ident] -> MetaTypePlus -> WithEnv ([Ident], MetaTypePlus)
discernMetaType is t = do
  is' <- mapM newNameWith is
  let nenv = Map.fromList $ zip (map asText is) is'
  t' <- discernMetaType' nenv t
  return (is', t')

discernMetaType' :: Map.HashMap T.Text Ident -> MetaTypePlus -> WithEnv MetaTypePlus
discernMetaType' nenv t =
  case t of
    (m, MetaTypeVar x) ->
      case Map.lookup (asText x) nenv of
        Just x' ->
          return (m, MetaTypeVar x')
        Nothing -> do
          eenv <- gets enumEnv
          if Map.member (asText x) eenv
            then return (m, MetaTypeEnum $ asText x)
            else case asText x of
              "i64" ->
                return (m, MetaTypeInt64)
              "code" ->
                return (m, MetaTypeAST)
              _ ->
                raiseError m $ "undefined type-variable: " <> asText x
    (m, MetaTypeArrow domList cod) -> do
      domList' <- mapM (discernMetaType' nenv) domList
      cod' <- discernMetaType' nenv cod
      return (m, MetaTypeArrow domList' cod')
    (m, MetaTypeNec t') -> do
      t'' <- discernMetaType' nenv t'
      return (m, MetaTypeNec t'')
    _ ->
      return t
