module Parse.Discern
  ( discern,
    discernIdentPlus,
  )
where

import Control.Monad.State.Lazy
import Data.Basic
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Log
import Data.Namespace
import qualified Data.Text as T
import Data.WeakTerm

type NameEnv = Map.HashMap T.Text Ident

discern :: WeakTermPlus -> WithEnv WeakTermPlus
discern e = do
  nenv <- gets topNameEnv
  discern' nenv e

discernIdentPlus :: WeakIdentPlus -> WithEnv WeakIdentPlus
discernIdentPlus (m, x, t) = do
  nenv <- gets topNameEnv
  when (Map.member (asText x) nenv) $
    raiseError m $ "the variable `" <> asText x <> "` is already defined at the top level"
  t' <- discern' nenv t
  x' <- newIdentFromIdent x
  modify (\env -> env {topNameEnv = Map.insert (asText x) x' nenv})
  return (m, x', t')

-- Alpha-convert all the variables so that different variables have different names.
discern' :: NameEnv -> WeakTermPlus -> WithEnv WeakTermPlus
discern' nenv term =
  case term of
    (m, WeakTermTau) ->
      return (m, WeakTermTau)
    (m, WeakTermVar _ (I (s, _))) ->
      tryCand (resolveSymbol m (asWeakVar m nenv) s) $ do
        renv <- gets revEnumEnv
        tryCand (resolveSymbol m (findThenModify renv (\x -> (m, WeakTermEnumIntro x))) s) $ do
          eenv <- gets enumEnv
          tryCand (resolveSymbol m (findThenModify eenv (\x -> (m, WeakTermEnum x))) s) $
            tryCand (resolveSymbol m (asWeakConstant m) s) $
              raiseError m $ "undefined variable: " <> s
    (m, WeakTermPi xts t) -> do
      (xts', t') <- discernBinder nenv xts t
      return (m, WeakTermPi xts' t')
    (m, WeakTermPiIntro opacity kind xts e) -> do
      case kind of
        LamKindFix xt -> do
          (xt' : xts', e') <- discernBinder nenv (xt : xts) e
          return (m, WeakTermPiIntro opacity (LamKindFix xt') xts' e')
        _ -> do
          (xts', e') <- discernBinder nenv xts e
          return (m, WeakTermPiIntro opacity kind xts' e')
    (m, WeakTermPiElim e es) -> do
      es' <- mapM (discern' nenv) es
      e' <- discern' nenv e
      return (m, WeakTermPiElim e' es')
    (m, WeakTermConst x) ->
      return (m, WeakTermConst x)
    (m, WeakTermAster h) ->
      return (m, WeakTermAster h)
    (m, WeakTermInt t x) -> do
      t' <- discern' nenv t
      return (m, WeakTermInt t' x)
    (m, WeakTermFloat t x) -> do
      t' <- discern' nenv t
      return (m, WeakTermFloat t' x)
    (m, WeakTermEnum s) ->
      return (m, WeakTermEnum s)
    (m, WeakTermEnumIntro x) ->
      return (m, WeakTermEnumIntro x)
    (m, WeakTermEnumElim (e, t) caseList) -> do
      e' <- discern' nenv e
      t' <- discern' nenv t
      caseList' <-
        forM caseList $ \((mCase, l), body) -> do
          l' <- discernEnumCase mCase l
          body' <- discern' nenv body
          return ((mCase, l'), body')
      return (m, WeakTermEnumElim (e', t') caseList')
    (m, WeakTermQuestion e t) -> do
      e' <- discern' nenv e
      t' <- discern' nenv t
      return (m, WeakTermQuestion e' t')
    (m, WeakTermDerangement i es) -> do
      es' <- mapM (discern' nenv) es
      return (m, WeakTermDerangement i es')
    (m, WeakTermCase resultType mSubject (e, t) clauseList) -> do
      resultType' <- discern' nenv resultType
      mSubject' <- mapM (discern' nenv) mSubject
      e' <- discern' nenv e
      t' <- discern' nenv t
      clauseList' <- forM clauseList $ \((constructorName, xts), body) -> do
        constructorName' <- resolveSymbol m (asItself m nenv) (asText constructorName)
        case constructorName' of
          Just (_, newName) -> do
            (xts', body') <- discernBinder nenv xts body
            return ((newName, xts'), body')
          Nothing ->
            raiseError m $ "no such constructor is defined: " <> asText constructorName
      return (m, WeakTermCase resultType' mSubject' (e', t') clauseList')

discernBinder ::
  NameEnv ->
  [WeakIdentPlus] ->
  WeakTermPlus ->
  WithEnv ([WeakIdentPlus], WeakTermPlus)
discernBinder nenv binder e =
  case binder of
    [] -> do
      e' <- discern' nenv e
      return ([], e')
    (mx, x, t) : xts -> do
      t' <- discern' nenv t
      x' <- newIdentFromIdent x
      (xts', e') <- discernBinder (Map.insert (asText x) x' nenv) xts e
      return ((mx, x', t') : xts', e')

discernEnumCase :: Hint -> EnumCase -> WithEnv EnumCase
discernEnumCase m weakCase =
  case weakCase of
    EnumCaseLabel l -> do
      renv <- gets revEnumEnv
      ml <- resolveSymbol m (findThenModify renv EnumCaseLabel) l
      case ml of
        Just l' ->
          return l'
        Nothing -> do
          e <- gets enumEnv
          p' e
          raiseError m $ "no such enum-value is defined: " <> l
    _ ->
      return weakCase
