module Parse.Discern
  ( discern,
    discernStmtList,
    discernTopLevelName,
  )
where

import Control.Monad
import Data.Basic
import Data.Global
import qualified Data.HashMap.Lazy as Map
import Data.IORef
import Data.Log
import Data.Namespace
import qualified Data.Text as T
import Data.WeakTerm

type NameEnv = Map.HashMap T.Text Ident

discern :: WeakTermPlus -> IO WeakTermPlus
discern e = do
  discern' Map.empty e

discernStmtList :: [WeakStmt] -> IO [WeakStmt]
discernStmtList stmtList =
  case stmtList of
    [] ->
      return []
    WeakStmtDef m x t e : rest -> do
      t' <- discern t
      e' <- discern e
      rest' <- discernStmtList rest
      return $ WeakStmtDef m x t' e' : rest'
    WeakStmtUse name : rest -> do
      use name
      discernStmtList rest
    WeakStmtUnuse name : rest -> do
      unuse name
      discernStmtList rest
    WeakStmtDefinePrefix from to : rest -> do
      modifyIORef' nsEnv $ \env -> (from, to) : env
      discernStmtList rest
    WeakStmtRemovePrefix from to : rest -> do
      modifyIORef' nsEnv $ \env -> filter (/= (from, to)) env
      discernStmtList rest

discernTopLevelName :: Bool -> Hint -> Ident -> IO Ident
discernTopLevelName isReducible m x = do
  let nameEnv = if isReducible then transparentTopNameEnv else opaqueTopNameEnv
  nenv <- readIORef nameEnv
  when (Map.member (asText x) nenv) $
    raiseError m $ "the variable `" <> asText x <> "` is already defined at the top level"
  x' <- newIdentFromIdent x
  path <- getCurrentFilePath
  modifyIORef' nameEnv $ \env -> Map.insert (asText x) (path, x') env
  return x'

-- Alpha-convert all the variables so that different variables have different names.
discern' :: NameEnv -> WeakTermPlus -> IO WeakTermPlus
discern' nenv term =
  case term of
    (m, WeakTermTau) ->
      return (m, WeakTermTau)
    (m, WeakTermVar _ (I (s, _))) -> do
      tryCand (resolveSymbol m (asWeakVar m nenv) s) $ do
        nenvTrans <- readIORef transparentTopNameEnv
        tryCand (resolveSymbol m (asTransparentGlobalVar m nenvTrans) s) $ do
          nenvOpaque <- readIORef opaqueTopNameEnv
          tryCand (resolveSymbol m (asOpaqueGlobalVar m nenvOpaque) s) $ do
            renv <- readIORef revEnumEnv
            tryCand (resolveSymbol m (asEnumIntro m renv) s) $ do
              eenv <- readIORef enumEnv
              tryCand (resolveSymbol m (asEnum m eenv) s) $
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
    (m, WeakTermEnum fp s) ->
      return (m, WeakTermEnum fp s)
    (m, WeakTermEnumIntro fp x) ->
      return (m, WeakTermEnumIntro fp x)
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
      nenvTrans <- readIORef transparentTopNameEnv
      clauseList' <- forM clauseList $ \((mCons, constructorName, xts), body) -> do
        constructorName' <- resolveSymbol m (asConstructor m nenvTrans) (asText constructorName)
        case constructorName' of
          Just (_, newName) -> do
            (xts', body') <- discernBinder nenv xts body
            return ((mCons, newName, xts'), body')
          Nothing ->
            raiseError m $ "no such constructor is defined: " <> asText constructorName
      return (m, WeakTermCase resultType' mSubject' (e', t') clauseList')
    (m, WeakTermIgnore e) -> do
      e' <- discern' nenv e
      return (m, WeakTermIgnore e')

discernBinder ::
  NameEnv ->
  [WeakIdentPlus] ->
  WeakTermPlus ->
  IO ([WeakIdentPlus], WeakTermPlus)
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

discernEnumCase :: Hint -> EnumCase -> IO EnumCase
discernEnumCase m weakCase =
  case weakCase of
    EnumCaseLabel _ l -> do
      renv <- readIORef revEnumEnv
      ml <- resolveSymbol m (asEnumLabel renv) l
      case ml of
        Just l' ->
          return l'
        Nothing -> do
          e <- readIORef enumEnv
          p' e
          raiseError m $ "no such enum-value is defined: " <> l
    _ ->
      return weakCase
