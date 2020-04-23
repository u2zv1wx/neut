module Parse.Discern
  ( discern,
    discernIdent,
    discernIdentPlus,
    discernDef,
    discernText,
  )
where

import Control.Monad.State.Lazy
import Data.Basic
import Data.Env
import qualified Data.HashMap.Lazy as Map
import qualified Data.Set as S
import qualified Data.Text as T
import Data.WeakTerm

type NameEnv = Map.HashMap T.Text Ident

discern :: WeakTermPlus -> WithEnv WeakTermPlus
discern e = do
  nenv <- gets topNameEnv
  discern' nenv e

discernDef :: Def -> WithEnv Def
discernDef (m, xt, xts, e) = do
  nenv <- gets topNameEnv
  (xt', xts', e') <- discernIter nenv xt xts e
  return (m, xt', xts', e')

discernText :: Meta -> T.Text -> WithEnv Ident
discernText m x = do
  nenv <- gets topNameEnv
  penv <- gets prefixEnv
  lookupName'' m penv nenv $ asIdent x

-- Alpha-convert all the variables so that different variables have different names.
discern' :: NameEnv -> WeakTermPlus -> WithEnv WeakTermPlus
discern' nenv term =
  case term of
    (m, WeakTermTau) ->
      return (m, WeakTermTau)
    (m, WeakTermUpsilon x@(I (s, _))) -> do
      penv <- gets prefixEnv
      mx <- lookupName m penv nenv x
      case mx of
        Just x' ->
          return (m, WeakTermUpsilon x')
        Nothing -> do
          b1 <- lookupEnumValueNameWithPrefix s
          case b1 of
            Just s' ->
              return (m, WeakTermEnumIntro (EnumValueLabel s'))
            Nothing -> do
              b2 <- lookupEnumTypeNameWithPrefix s
              case b2 of
                Just s' ->
                  return (m, WeakTermEnum (EnumTypeLabel s'))
                Nothing -> do
                  mc <- lookupConstantMaybe m penv s
                  case mc of
                    Just c ->
                      return (m, WeakTermConst c)
                    Nothing ->
                      raiseError m $ "undefined variable:  " <> asText x
    (m, WeakTermPi mName xts t) -> do
      (xts', t') <- discernBinder nenv xts t
      return (m, WeakTermPi mName xts' t')
    (m, WeakTermPiIntro info xts e) -> do
      (xts', e') <- discernBinder nenv xts e
      case info of
        Nothing ->
          return (m, WeakTermPiIntro Nothing xts' e')
        Just (indName, consName, args) -> do
          penv <- gets prefixEnv
          indName' <- lookupName'' m penv nenv indName
          args' <- mapM (discernFreeIdentPlus nenv) args
          return (m, WeakTermPiIntro (Just (indName', consName, args')) xts' e')
    (m, WeakTermPiElim e es) -> do
      es' <- mapM (discern' nenv) es
      e' <- discern' nenv e
      return (m, WeakTermPiElim e' es')
    (m, WeakTermIter (mx, x, t) xts e) -> do
      (xt', xts', e') <- discernIter nenv (mx, x, t) xts e
      return (m, WeakTermIter xt' xts' e')
    (m, WeakTermConst x) ->
      return (m, WeakTermConst x)
    (m, WeakTermBoxElim x) ->
      return (m, WeakTermBoxElim x)
    (m, WeakTermHole h) ->
      return (m, WeakTermHole h)
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
          l' <- discernWeakCase mCase nenv l
          body' <- discern' nenv body
          return ((mCase, l'), body')
      return (m, WeakTermEnumElim (e', t') caseList')
    (m, WeakTermArray dom kind) -> do
      dom' <- discern' nenv dom
      return (m, WeakTermArray dom' kind)
    (m, WeakTermArrayIntro kind es) -> do
      es' <- mapM (discern' nenv) es
      return (m, WeakTermArrayIntro kind es')
    (m, WeakTermArrayElim kind xts e1 e2) -> do
      e1' <- discern' nenv e1
      (xts', e2') <- discernBinder nenv xts e2
      return (m, WeakTermArrayElim kind xts' e1' e2')
    (m, WeakTermStruct ts) ->
      return (m, WeakTermStruct ts)
    (m, WeakTermStructIntro ets) -> do
      let (es, ts) = unzip ets
      es' <- mapM (discern' nenv) es
      return (m, WeakTermStructIntro $ zip es' ts)
    (m, WeakTermStructElim xts e1 e2) -> do
      e1' <- discern' nenv e1
      (xts', e2') <- discernStruct nenv xts e2
      return (m, WeakTermStructElim xts' e1' e2')
    (m, WeakTermCase indInfo e cxtes) -> do
      e' <- discern' nenv e
      penv <- gets prefixEnv
      cxtes' <-
        flip mapM cxtes $ \(((mc, c), xts), body) -> do
          c' <- lookupName'' mc penv nenv c
          (xts', body') <- discernBinder nenv xts body
          return (((mc, c'), xts'), body')
      case indInfo of
        Nothing ->
          return (m, WeakTermCase Nothing e' cxtes')
        Just indName -> do
          indName' <- lookupName'' m penv nenv indName
          return (m, WeakTermCase (Just indName') e' cxtes')
    (m, WeakTermQuestion e t) -> do
      e' <- discern' nenv e
      t' <- discern' nenv t
      return (m, WeakTermQuestion e' t')
    (_, WeakTermErase mxs e) -> do
      penv <- gets prefixEnv
      forM_ mxs $ \(mx, x) -> lookupName'' mx penv nenv (asIdent x)
      let xs = map snd mxs
      let nenv' = Map.filterWithKey (\k _ -> k `notElem` xs) nenv
      discern' nenv' e

discernFreeIdentPlus :: NameEnv -> WeakIdentPlus -> WithEnv WeakIdentPlus
discernFreeIdentPlus nenv (m, x, t) = do
  t' <- discern' nenv t
  penv <- gets prefixEnv
  x' <- lookupName'' m penv nenv x
  return (m, x', t')

discernIdent :: Meta -> Ident -> WithEnv (Meta, Ident)
discernIdent m x = do
  x' <- newDefinedNameWith m x
  modify (\env -> env {topNameEnv = Map.insert (asText x) x' (topNameEnv env)})
  return (m, x')

discernIdentPlus :: WeakIdentPlus -> WithEnv WeakIdentPlus
discernIdentPlus (m, x, t) = do
  nenv <- gets topNameEnv
  t' <- discern' nenv t
  x' <- newDefinedNameWith m x
  modify (\env -> env {topNameEnv = Map.insert (asText x) x' (topNameEnv env)})
  return (m, x', t')

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
      x' <- newDefinedNameWith mx x
      (xts', e') <- discernBinder (insertName x x' nenv) xts e
      return ((mx, x', t') : xts', e')

discernIter ::
  NameEnv ->
  WeakIdentPlus ->
  [WeakIdentPlus] ->
  WeakTermPlus ->
  WithEnv (WeakIdentPlus, [WeakIdentPlus], WeakTermPlus)
discernIter nenv (mf, f, tf) binder e = do
  tf' <- discern' nenv tf
  discernIter' nenv (mf, f, tf') binder e

discernIter' ::
  NameEnv ->
  WeakIdentPlus ->
  [WeakIdentPlus] ->
  WeakTermPlus ->
  WithEnv (WeakIdentPlus, [WeakIdentPlus], WeakTermPlus)
discernIter' nenv self@(mf, f, tf') binder e =
  case binder of
    [] -> do
      f' <- newDefinedNameWith mf f
      e' <- discern' (insertName f f' nenv) e
      return ((mf, f', tf'), [], e')
    ((mx, x, t) : xts) -> do
      t' <- discern' nenv t
      x' <- newDefinedNameWith mx x
      (self', xts', e') <- discernIter' (insertName x x' nenv) self xts e
      return (self', (mx, x', t') : xts', e')

discernWeakCase :: Meta -> NameEnv -> WeakCase -> WithEnv WeakCase
discernWeakCase m nenv weakCase =
  case weakCase of
    WeakCaseInt t a -> do
      t' <- discern' nenv t
      return (WeakCaseInt t' a)
    WeakCaseLabel l -> do
      ml <- lookupEnumValueNameWithPrefix l
      case ml of
        Just l' ->
          return (WeakCaseLabel l')
        Nothing ->
          raiseError m $ "no such enum-value is defined: " <> l
    _ ->
      return weakCase

discernStruct ::
  NameEnv ->
  [(Meta, Ident, ArrayKind)] ->
  WeakTermPlus ->
  WithEnv ([(Meta, Ident, ArrayKind)], WeakTermPlus)
discernStruct nenv binder e =
  case binder of
    [] -> do
      e' <- discern' nenv e
      return ([], e')
    ((mx, x, t) : xts) -> do
      x' <- newDefinedNameWith mx x
      (xts', e') <- discernStruct (insertName x x' nenv) xts e
      return ((mx, x', t) : xts', e')

newDefinedNameWith :: Meta -> Ident -> WithEnv Ident
newDefinedNameWith m (I (s, _)) = do
  j <- newCount
  modify (\env -> env {nameEnv = Map.insert s s (nameEnv env)})
  let x = I (s, j)
  insertIntoIntactSet m s
  return x

insertName :: Ident -> Ident -> NameEnv -> NameEnv
insertName (I (s, _)) =
  Map.insert s

insertIntoIntactSet :: Meta -> T.Text -> WithEnv ()
insertIntoIntactSet m x =
  whenCheck $ modify (\env -> env {intactSet = S.insert (m, x) (intactSet env)})

removeFromIntactSet :: Meta -> T.Text -> WithEnv ()
removeFromIntactSet m x =
  whenCheck $ modify (\env -> env {intactSet = S.delete (m, x) (intactSet env)})

lookupName :: Meta -> [T.Text] -> NameEnv -> Ident -> WithEnv (Maybe Ident)
lookupName m penv nenv x =
  case Map.lookup (asText x) nenv of
    Just x' -> do
      removeFromIntactSet m $ asText x'
      return $ Just x'
    Nothing ->
      lookupName' m penv nenv x

lookupName' :: Meta -> [T.Text] -> NameEnv -> Ident -> WithEnv (Maybe Ident)
lookupName' m penv nenv x =
  case penv of
    [] ->
      return Nothing
    prefix : prefixList -> do
      let query = prefix <> ":" <> asText x
      case Map.lookup query nenv of
        Nothing ->
          lookupName' m prefixList nenv x
        Just x' -> do
          removeFromIntactSet m query
          return $ Just x'

lookupName'' :: Meta -> [T.Text] -> NameEnv -> Ident -> WithEnv Ident
lookupName'' m penv nenv x = do
  mx <- lookupName m penv nenv x
  case mx of
    Just x' ->
      return x'
    Nothing ->
      raiseError m $ "(double-prime) undefined variable: " <> asText x

lookupConstantMaybe :: Meta -> [T.Text] -> T.Text -> WithEnv (Maybe T.Text)
lookupConstantMaybe m penv x = do
  b <- isConstant x
  if b
    then do
      removeFromIntactSet m x
      return $ Just x
    else lookupConstantMaybe' m penv x

lookupConstantMaybe' :: Meta -> [T.Text] -> T.Text -> WithEnv (Maybe T.Text)
lookupConstantMaybe' m penv x =
  case penv of
    [] ->
      return Nothing
    prefix : prefixList -> do
      let query = prefix <> ":" <> x
      b <- isConstant query
      if b
        then do
          removeFromIntactSet m query
          return $ Just query
        else lookupConstantMaybe' m prefixList x

lookupEnum :: (T.Text -> WithEnv Bool) -> T.Text -> WithEnv (Maybe T.Text)
lookupEnum f name = do
  b <- f name
  if b
    then return $ Just name
    else do
      penv <- gets prefixEnv
      lookupEnum' f penv name

lookupEnum' :: (T.Text -> WithEnv Bool) -> [T.Text] -> T.Text -> WithEnv (Maybe T.Text)
lookupEnum' f penv name =
  case penv of
    [] ->
      return Nothing
    prefix : prefixList -> do
      let name' = prefix <> ":" <> name
      b <- f name'
      if b
        then return $ Just name'
        else lookupEnum' f prefixList name

lookupEnumValueNameWithPrefix :: T.Text -> WithEnv (Maybe T.Text)
lookupEnumValueNameWithPrefix =
  lookupEnum isDefinedEnumValue

lookupEnumTypeNameWithPrefix :: T.Text -> WithEnv (Maybe T.Text)
lookupEnumTypeNameWithPrefix =
  lookupEnum isDefinedEnumType

isDefinedEnumValue :: T.Text -> WithEnv Bool
isDefinedEnumValue name = do
  renv <- gets revEnumEnv
  return $ name `Map.member` renv

isDefinedEnumType :: T.Text -> WithEnv Bool
isDefinedEnumType name = do
  eenv <- gets enumEnv
  return $ name `Map.member` eenv
