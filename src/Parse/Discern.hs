{-# LANGUAGE OverloadedStrings #-}

module Parse.Discern
  ( discern
  ) where

import Control.Monad.Except
import Control.Monad.State

import qualified Data.HashMap.Strict as Map
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Set as S
import qualified Data.Text as T

import Data.Basic
import Data.Env
import Data.WeakTerm

discern :: [QuasiStmt] -> WithEnv [QuasiStmt]
discern = discern' Map.empty

type NameEnv = Map.HashMap T.Text Identifier

discern' :: NameEnv -> [QuasiStmt] -> WithEnv [QuasiStmt]
discern' _ [] = return []
discern' nenv ((QuasiStmtLet m (mx, x, t) e):ss) = do
  t' <- discern'' nenv t
  x' <- newDefinedNameWith' mx nenv x
  e' <- discern'' nenv e
  ss' <- discern' (insertName x x' nenv) ss
  return $ QuasiStmtLet m (mx, x', t') e' : ss'
discern' nenv ((QuasiStmtLetWT m (mx, x, t) e):ss) = do
  set <- gets unusedNameSet
  t' <- discern'' nenv t
  x' <- newDefinedNameWith' mx nenv x
  e' <- discern'' nenv e
  set' <- gets unusedNameSet
  modify (\env -> env {unusedNameSet = S.intersection set set'})
  ss' <- discern' (insertName x x' nenv) ss
  return $ QuasiStmtLetWT m (mx, x', t') e' : ss'
discern' nenv ((QuasiStmtDef xds):ss) = do
  let (xs, ds) = unzip xds
  -- discern for deflist
  let mys = map (\(_, (my, y, _), _, _) -> (my, y)) ds
  ys' <- mapM (\(my, y) -> newDefinedNameWith' my nenv y) mys
  let yis = map (asText . snd) mys
  let nenvForDef = Map.fromList (zip yis ys') `Map.union` nenv
  ds' <- mapM (discernDef nenvForDef) ds
  -- discern for continuation
  let ms = map (\(m, _, _, _) -> m) ds
  xs' <- zipWithM (\m x -> newDefinedNameWith m x) ms xs
  let xis = map asText xs
  let nenvForCont = Map.fromList (zip xis xs') `Map.union` nenv
  ss' <- discern' nenvForCont ss
  return $ QuasiStmtDef (zip xs' ds') : ss'
discern' nenv ((QuasiStmtConstDecl m (mx, x, t)):ss) = do
  t' <- discern'' nenv t
  ss' <- discern' nenv ss
  return $ QuasiStmtConstDecl m (mx, x, t') : ss'
discern' nenv ((QuasiStmtVerify m e):ss) = do
  e' <- discern'' nenv e
  ss' <- discern' nenv ss
  return $ QuasiStmtVerify m e' : ss'
discern' nenv ((QuasiStmtImplicit m x i):ss) = do
  set <- gets unusedNameSet
  penv <- gets prefixEnv
  x' <-
    do mc <- lookupConstantMaybe m penv (asText x)
       case mc of
         Just c -> return c
         Nothing -> lookupName'' m penv nenv x
  ienv <- gets introEnv
  when (S.member (asInt x') ienv) $ do
    raiseError m $
      "modifying implicit attribute of a constructor `" <>
      asText x' <> "` is prohibited"
  modify (\env -> env {unusedNameSet = set})
  ss' <- discern' nenv ss
  return $ QuasiStmtImplicit m x' i : ss'
discern' nenv ((QuasiStmtEnum m name xis):ss) = do
  insEnumEnv m name xis
  discern' nenv ss
discern' nenv ((QuasiStmtLetInductive n m (mx, a, t) e):ss) = do
  set <- gets unusedNameSet
  t' <- discern'' nenv t
  a' <- newDefinedNameWith' m nenv a
  e' <- discern'' nenv e
  set' <- gets unusedNameSet
  modify (\env -> env {unusedNameSet = S.intersection set set'})
  ss' <- discern' (insertName a a' nenv) ss
  return $ QuasiStmtLetInductive n m (mx, a', t') e' : ss'
discern' nenv ((QuasiStmtLetInductiveIntro m (mx, x, t) e as):ss) = do
  set <- gets unusedNameSet
  t' <- discern'' nenv t
  x' <- newDefinedNameWith' m nenv x
  e' <- discern'' nenv e
  penv <- gets prefixEnv
  as' <- mapM (lookupName'' m penv nenv) as
  set' <- gets unusedNameSet
  modify (\env -> env {unusedNameSet = S.intersection set set'})
  ss' <- discern' (insertName x x' nenv) ss
  return $ QuasiStmtLetInductiveIntro m (mx, x', t') e' as' : ss'
discern' nenv ((QuasiStmtUse prefix):ss) = do
  modify (\e -> e {prefixEnv = prefix : prefixEnv e})
  discern' nenv ss
discern' nenv ((QuasiStmtUnuse prefix):ss) = do
  modify (\e -> e {prefixEnv = filter (/= prefix) (prefixEnv e)})
  discern' nenv ss

discernDef :: NameEnv -> Def -> WithEnv Def
discernDef nenv (m, (mx, x, t), xts, e) = do
  t' <- discern'' nenv t
  (xts', e') <- discernBinder nenv xts e
  penv <- gets prefixEnv
  x' <- lookupName'' mx penv nenv x
  return (m, (mx, x', t'), xts', e')

-- Alpha-convert all the variables so that different variables have different names.
discern'' :: NameEnv -> WeakTermPlus -> WithEnv WeakTermPlus
discern'' _ (m, WeakTermTau) = return (m, WeakTermTau)
discern'' nenv (m, WeakTermUpsilon x@(I (s, _))) = do
  penv <- gets prefixEnv
  mx <- lookupName m penv nenv x
  b1 <- lookupEnumValueNameWithPrefix s
  b2 <- lookupEnumTypeNameWithPrefix s
  mc <- lookupConstantMaybe m penv s
  case (mx, b1, b2, mc) of
    (Just x', _, _, _) -> return (m, WeakTermUpsilon x')
    (_, Just s', _, _) -> return (m, WeakTermEnumIntro (EnumValueLabel s'))
    (_, _, Just s', _) -> return (m, WeakTermEnum (EnumTypeLabel s'))
    (_, _, _, Just c) -> return (m, WeakTermConst c)
    _ -> raiseError m $ "undefined variable:  " <> asText x
discern'' nenv (m, WeakTermPi mName xts t) = do
  (xts', t') <- discernBinder nenv xts t
  return (m, WeakTermPi mName xts' t')
discern'' nenv (m, WeakTermPiIntro xts e) = do
  (xts', e') <- discernBinder nenv xts e
  return (m, WeakTermPiIntro xts' e')
discern'' nenv (m, WeakTermPiIntroNoReduce xts e) = do
  (xts', e') <- discernBinder nenv xts e
  return (m, WeakTermPiIntroNoReduce xts' e')
discern'' nenv (m, WeakTermPiIntroPlus ind (name, is, args1, args2) xts e) = do
  penv <- gets prefixEnv
  ind' <- lookupName'' m penv nenv ind
  args' <- mapM (discernIdentPlus nenv) (args1 ++ args2)
  let args1' = take (length args1) args'
  let args2' = drop (length args1) args'
  (xts', e') <- discernBinder nenv xts e
  return (m, WeakTermPiIntroPlus ind' (name, is, args1', args2') xts' e')
discern'' nenv (m, WeakTermPiElim e es) = do
  es' <- mapM (discern'' nenv) es
  e' <- discern'' nenv e
  return (m, WeakTermPiElim e' es')
discern'' nenv (m, WeakTermIter (mx, x, t) xts e) = do
  t' <- discern'' nenv t
  (xt', xts', e') <- discernIter nenv (mx, x, t') xts e
  return (m, WeakTermIter xt' xts' e')
discern'' _ (m, WeakTermConst x) = return (m, WeakTermConst x)
discern'' _ (m, WeakTermZeta h) = do
  return (m, WeakTermZeta h)
discern'' nenv (m, WeakTermInt t x) = do
  t' <- discern'' nenv t
  return (m, WeakTermInt t' x)
discern'' _ (m, WeakTermFloat16 x) = return (m, WeakTermFloat16 x)
discern'' _ (m, WeakTermFloat32 x) = return (m, WeakTermFloat32 x)
discern'' _ (m, WeakTermFloat64 x) = return (m, WeakTermFloat64 x)
discern'' nenv (m, WeakTermFloat t x) = do
  t' <- discern'' nenv t
  return (m, WeakTermFloat t' x)
discern'' _ (m, WeakTermEnum s) = return (m, WeakTermEnum s)
discern'' _ (m, WeakTermEnumIntro x) = return (m, WeakTermEnumIntro x)
discern'' nenv (m, WeakTermEnumElim (e, t) caseList) = do
  e' <- discern'' nenv e
  t' <- discern'' nenv t
  caseList' <-
    forM caseList $ \((mCase, l), body) -> do
      l' <- discernWeakCase mCase nenv l
      body' <- discern'' nenv body
      return ((mCase, l'), body')
  return (m, WeakTermEnumElim (e', t') caseList')
discern'' nenv (m, WeakTermArray dom kind) = do
  dom' <- discern'' nenv dom
  return (m, WeakTermArray dom' kind)
discern'' nenv (m, WeakTermArrayIntro kind es) = do
  es' <- mapM (discern'' nenv) es
  return (m, WeakTermArrayIntro kind es')
discern'' nenv (m, WeakTermArrayElim kind xts e1 e2) = do
  e1' <- discern'' nenv e1
  (xts', e2') <- discernBinder nenv xts e2
  return (m, WeakTermArrayElim kind xts' e1' e2')
discern'' _ (m, WeakTermStruct ts) = return (m, WeakTermStruct ts)
discern'' nenv (m, WeakTermStructIntro ets) = do
  let (es, ts) = unzip ets
  es' <- mapM (discern'' nenv) es
  return (m, WeakTermStructIntro $ zip es' ts)
discern'' nenv (m, WeakTermStructElim xts e1 e2) = do
  e1' <- discern'' nenv e1
  (xts', e2') <- discernStruct nenv xts e2
  return (m, WeakTermStructElim xts' e1' e2')
discern'' nenv (m, WeakTermCase indName e cxtes) = do
  e' <- discern'' nenv e
  penv <- gets prefixEnv
  cxtes' <-
    flip mapM cxtes $ \(((mc, c), xts), body) -> do
      (expandedName, c') <- lookupConsName mc penv nenv c
      label <- lookupLLVMEnumEnv mc expandedName
      renv <- gets revCaseEnv
      modify (\env -> env {revCaseEnv = IntMap.insert (asInt c') label renv})
      (xts', body') <- discernBinder nenv xts body
      return (((mc, c'), xts'), body')
  return (m, WeakTermCase indName e' cxtes')
discern'' nenv (m, WeakTermWithNote e t) = do
  e' <- discern'' nenv e
  t' <- discern'' nenv t
  return (m, WeakTermWithNote e' t')
discern'' nenv (_, WeakTermErase mxs e) = do
  penv <- gets prefixEnv
  forM_ mxs $ \(mx, x) -> lookupName'' mx penv nenv (asIdent x)
  let xs = map snd mxs
  let nenv' = Map.filterWithKey (\k _ -> k `notElem` xs) nenv
  discern'' nenv' e

discernBinder ::
     NameEnv
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> WithEnv ([IdentifierPlus], WeakTermPlus)
discernBinder nenv [] e = do
  e' <- discern'' nenv e
  return ([], e')
discernBinder nenv ((mx, x, t):xts) e = do
  t' <- discern'' nenv t
  x' <- newDefinedNameWith mx x
  (xts', e') <- discernBinder (insertName x x' nenv) xts e
  return ((mx, x', t') : xts', e')

discernIdentPlus :: NameEnv -> IdentifierPlus -> WithEnv IdentifierPlus
discernIdentPlus nenv (m, x, t) = do
  t' <- discern'' nenv t
  penv <- gets prefixEnv
  x' <- lookupName'' m penv nenv x
  return (m, x', t')

discernIter ::
     NameEnv
  -> IdentifierPlus
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> WithEnv (IdentifierPlus, [IdentifierPlus], WeakTermPlus)
discernIter nenv (mx, x, t') [] e = do
  x' <- newDefinedNameWith mx x
  e' <- discern'' (insertName x x' nenv) e
  return ((mx, x', t'), [], e')
discernIter nenv xt ((mx, x, t):xts) e = do
  t' <- discern'' nenv t
  x' <- newDefinedNameWith mx x
  (xt', xts', e') <- discernIter (insertName x x' nenv) xt xts e
  return (xt', (mx, x', t') : xts', e')

discernWeakCase :: Meta -> NameEnv -> WeakCase -> WithEnv WeakCase
discernWeakCase _ nenv (WeakCaseInt t a) = do
  t' <- discern'' nenv t
  return (WeakCaseInt t' a)
discernWeakCase m _ (WeakCaseLabel l) = do
  ml <- lookupEnumValueNameWithPrefix l
  case ml of
    Just l' -> return (WeakCaseLabel l')
    Nothing -> raiseError m $ "no such enum-value is defined: " <> l
discernWeakCase _ _ l = return l

discernStruct ::
     NameEnv
  -> [(Meta, Identifier, ArrayKind)]
  -> WeakTermPlus
  -> WithEnv ([(Meta, Identifier, ArrayKind)], WeakTermPlus)
discernStruct nenv [] e = do
  e' <- discern'' nenv e
  return ([], e')
discernStruct nenv ((mx, x, t):xts) e = do
  x' <- newDefinedNameWith mx x
  (xts', e') <- discernStruct (insertName x x' nenv) xts e
  return ((mx, x', t) : xts', e')

newDefinedNameWith :: Meta -> Identifier -> WithEnv Identifier
newDefinedNameWith m (I (s, _)) = do
  j <- newCount
  modify (\env -> env {nameEnv = Map.insert s s (nameEnv env)})
  let x = I (s, j)
  modify (\env -> env {unusedNameSet = S.insert (m, x) (unusedNameSet env)})
  return x

newDefinedNameWith' :: Meta -> NameEnv -> Identifier -> WithEnv Identifier
newDefinedNameWith' m nenv x = do
  case Map.lookup (asText x) nenv of
    Nothing -> newDefinedNameWith m x
    Just _ ->
      raiseError m $
      "the identifier `" <> asText x <> "` is already defined at top level"

insertName :: Identifier -> Identifier -> NameEnv -> NameEnv
insertName (I (s, _)) y nenv = Map.insert s y nenv

lookupName ::
     Meta -> [T.Text] -> NameEnv -> Identifier -> WithEnv (Maybe Identifier)
lookupName m penv nenv x =
  case Map.lookup (asText x) nenv of
    Just x' -> do
      modify
        (\env -> env {unusedNameSet = S.delete (m, x') (unusedNameSet env)})
      return $ Just x'
    Nothing -> lookupName' m penv nenv x

lookupName' ::
     Meta -> [T.Text] -> NameEnv -> Identifier -> WithEnv (Maybe Identifier)
lookupName' _ [] _ _ = return Nothing
lookupName' m (prefix:prefixList) nenv x =
  case Map.lookup (prefix <> ":" <> asText x) nenv of
    Just x' -> do
      modify
        (\env -> env {unusedNameSet = S.delete (m, x') (unusedNameSet env)})
      return $ Just x'
    Nothing -> lookupName' m prefixList nenv x

lookupName'' :: Meta -> [T.Text] -> NameEnv -> Identifier -> WithEnv Identifier
lookupName'' m penv nenv x = do
  mx <- lookupName m penv nenv x
  case mx of
    Just x' -> return x'
    Nothing -> raiseError m $ "undefined variable: " <> asText x

lookupConsName ::
     Meta -> [T.Text] -> NameEnv -> Identifier -> WithEnv (T.Text, Identifier)
lookupConsName m penv nenv x =
  case Map.lookup (asText x) nenv of
    Just x' -> return (asText x, x')
    Nothing -> lookupConsName' m penv nenv x

lookupConsName' ::
     Meta -> [T.Text] -> NameEnv -> Identifier -> WithEnv (T.Text, Identifier)
lookupConsName' m [] _ x = raiseError m $ "undefined variable: " <> asText x
lookupConsName' m (prefix:prefixList) nenv x = do
  let query = prefix <> ":" <> asText x
  case Map.lookup query nenv of
    Just x' -> return (query, x')
    Nothing -> lookupConsName' m prefixList nenv x

lookupEnum :: (T.Text -> WithEnv Bool) -> T.Text -> WithEnv (Maybe T.Text)
lookupEnum f name = do
  b <- f name
  if b
    then return $ Just name
    else do
      penv <- gets prefixEnv
      lookupEnum' f penv name

lookupEnum' ::
     (T.Text -> WithEnv Bool) -> [T.Text] -> T.Text -> WithEnv (Maybe T.Text)
lookupEnum' _ [] _ = return Nothing
lookupEnum' f (prefix:prefixList) name = do
  let name' = prefix <> ":" <> name
  b <- f name'
  if b
    then return $ Just name'
    else lookupEnum' f prefixList name

lookupEnumValueNameWithPrefix :: T.Text -> WithEnv (Maybe T.Text)
lookupEnumValueNameWithPrefix name = lookupEnum isDefinedEnumValue name

lookupEnumTypeNameWithPrefix :: T.Text -> WithEnv (Maybe T.Text)
lookupEnumTypeNameWithPrefix name = lookupEnum isDefinedEnumType name

isDefinedEnumValue :: T.Text -> WithEnv Bool
isDefinedEnumValue name = do
  renv <- gets revEnumEnv
  return $ name `Map.member` renv

isDefinedEnumType :: T.Text -> WithEnv Bool
isDefinedEnumType name = do
  eenv <- gets enumEnv
  return $ name `Map.member` eenv
