module Parse.Discern
  ( discern,
    discernIdentPlus,
    discernDef,
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

discernDef :: Def -> WithEnv Def
discernDef (m, xt, xts, e) = do
  nenv <- gets topNameEnv
  (xt', xts', e') <- discernFix nenv xt xts e
  return (m, xt', xts', e')

-- Alpha-convert all the variables so that different variables have different names.
discern' :: NameEnv -> WeakTermPlus -> WithEnv WeakTermPlus
discern' nenv term =
  case term of
    (m, WeakTermTau) ->
      return (m, WeakTermTau)
    (m, WeakTermVar (I (s, _))) ->
      tryCand (resolveSymbol m (asWeakVar m nenv) s) $
        tryCand (resolveSymbol m (asWeakEnumValue m) s) $
          tryCand (resolveSymbol m (asWeakEnumType m) s) $
            tryCand (resolveSymbol m (asWeakConstant m) s) $
              raiseError m $ "undefined variable: " <> s
    (m, WeakTermPi xts t) -> do
      (xts', t') <- discernBinder nenv xts t
      return (m, WeakTermPi xts' t')
    (m, WeakTermPiIntro mName xts e) -> do
      (xts', e') <- discernBinder nenv xts e
      return (m, WeakTermPiIntro mName xts' e')
    (m, WeakTermPiElim e es) -> do
      es' <- mapM (discern' nenv) es
      e' <- discern' nenv e
      return (m, WeakTermPiElim e' es')
    (m, WeakTermFix (mx, x, t) xts e) -> do
      (xt', xts', e') <- discernFix nenv (mx, x, t) xts e
      return (m, WeakTermFix xt' xts' e')
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
    (m, WeakTermTensor ts) -> do
      ts' <- mapM (discern' nenv) ts
      return (m, WeakTermTensor ts')
    (m, WeakTermTensorIntro es) -> do
      es' <- mapM (discern' nenv) es
      return (m, WeakTermTensorIntro es')
    (m, WeakTermTensorElim xts e1 e2) -> do
      e1' <- discern' nenv e1
      (xts', e2') <- discernBinder nenv xts e2
      return (m, WeakTermTensorElim xts' e1' e2')
    (m, WeakTermQuestion e t) -> do
      e' <- discern' nenv e
      t' <- discern' nenv t
      return (m, WeakTermQuestion e' t')
    (m, WeakTermDerangement i resultType ekts) -> do
      resultType' <- discern' nenv resultType
      let (es, ks, ts) = unzip3 ekts
      es' <- mapM (discern' nenv) es
      ts' <- mapM (discern' nenv) ts
      return (m, WeakTermDerangement i resultType' (zip3 es' ks ts'))
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

discernFix ::
  NameEnv ->
  WeakIdentPlus ->
  [WeakIdentPlus] ->
  WeakTermPlus ->
  WithEnv (WeakIdentPlus, [WeakIdentPlus], WeakTermPlus)
discernFix nenv self binder e = do
  (binder', e') <- discernBinder nenv (self : binder) e
  return (head binder', tail binder', e')

discernEnumCase :: Hint -> EnumCase -> WithEnv EnumCase
discernEnumCase m weakCase =
  case weakCase of
    EnumCaseLabel l -> do
      ml <- resolveSymbol m asEnumCase l
      case ml of
        Just l' ->
          return l'
        Nothing -> do
          e <- gets enumEnv
          p' e
          raiseError m $ "no such enum-value is defined: " <> l
    _ ->
      return weakCase
