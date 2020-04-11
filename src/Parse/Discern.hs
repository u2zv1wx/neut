{-# LANGUAGE OverloadedStrings #-}

module Parse.Discern
  ( discern
  ) where

import Control.Monad.Except
import Control.Monad.State

import qualified Data.HashMap.Strict as Map
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
  e' <- discern'' nenv e
  insertConstant mx x
  ss' <- discern' nenv ss -- xはconstだからnenvの更新の必要なし
  return $ QuasiStmtLet m (mx, x, t') e' : ss'
discern' nenv ((QuasiStmtLetWT m (mx, x, t) e):ss) = do
  set <- gets intactSet
  t' <- discern'' nenv t
  e' <- discern'' nenv e
  set' <- gets intactSet
  whenCheck $ modify (\env -> env {intactSet = S.intersection set set'})
  insertConstant mx x
  ss' <- discern' nenv ss
  return $ QuasiStmtLetWT m (mx, x, t') e' : ss'
discern' nenv ((QuasiStmtDef xds):ss) = do
  forM_ xds $ \(x, (m, _, _, _)) -> insertConstant m x
  let (xs, ds) = unzip xds
  ds' <- mapM (discernDef nenv) ds
  ss' <- discern' nenv ss
  return $ QuasiStmtDef (zip xs ds') : ss'
discern' nenv ((QuasiStmtConstDecl m (mx, x, t)):ss) = do
  t' <- discern'' nenv t
  ss' <- discern' nenv ss
  return $ QuasiStmtConstDecl m (mx, x, t') : ss'
discern' nenv ((QuasiStmtVerify m e):ss) = do
  e' <- discern'' nenv e
  ss' <- discern' nenv ss
  return $ QuasiStmtVerify m e' : ss'
discern' nenv ((QuasiStmtImplicit m x i):ss) = do
  penv <- gets prefixEnv
  x' <- lookupConstant m penv x
  ss' <- discern' nenv ss
  return $ QuasiStmtImplicit m x' i : ss'
discern' nenv ((QuasiStmtEnum m name xis):ss) = do
  insEnumEnv m name xis
  discern' nenv ss
discern' nenv ((QuasiStmtLetInductive n m (mx, a, t) e):ss) = do
  set <- gets intactSet
  t' <- discern'' nenv t
  e' <- discern'' nenv e
  set' <- gets intactSet
  whenCheck $ modify (\env -> env {intactSet = S.intersection set set'})
  insertConstant mx a
  ss' <- discern' nenv ss
  return $ QuasiStmtLetInductive n m (mx, a, t') e' : ss'
discern' nenv ((QuasiStmtLetInductiveIntro m (mx, x, t) e as):ss) = do
  set <- gets intactSet
  t' <- discern'' nenv t
  e' <- discern'' nenv e
  set' <- gets intactSet
  whenCheck $ modify (\env -> env {intactSet = S.intersection set set'})
  insertConstant mx x
  ss' <- discern' nenv ss
  return $ QuasiStmtLetInductiveIntro m (mx, x, t') e' as : ss'
discern' nenv ((QuasiStmtUse prefix):ss) = do
  modify (\e -> e {prefixEnv = prefix : prefixEnv e})
  discern' nenv ss
discern' nenv ((QuasiStmtUnuse prefix):ss) = do
  modify (\e -> e {prefixEnv = filter (/= prefix) (prefixEnv e)})
  discern' nenv ss

discernDef :: NameEnv -> Def -> WithEnv Def
discernDef nenv (m, (mx, x, t), xts, e) = do
  t' <- discern'' nenv t
  x' <- newDefinedNameWith mx x
  (xts', e') <- discernBinder (insertName x x' nenv) xts e
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
    (_, _, _, Just c) -> return (m, WeakTermConst c)
    (_, Just s', _, _) -> return (m, WeakTermEnumIntro (EnumValueLabel s'))
    (_, _, Just s', _) -> return (m, WeakTermEnum (EnumTypeLabel s'))
    _ -> raiseError m $ "(*) undefined variable:  " <> asText x
discern'' nenv (m, WeakTermPi mName xts t) = do
  (xts', t') <- discernBinder nenv xts t
  return (m, WeakTermPi mName xts' t')
discern'' nenv (m, WeakTermPiIntro xts e) = do
  (xts', e') <- discernBinder nenv xts e
  return (m, WeakTermPiIntro xts' e')
discern'' nenv (m, WeakTermPiIntroPlus ind (name, args) xts e) = do
  args' <- mapM (discernIdentPlus nenv) args
  (xts', e') <- discernBinder nenv xts e
  return (m, WeakTermPiIntroPlus ind (name, args') xts' e')
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
      c' <- lookupConstant mc penv c
      -- c' <- lookupConsName mc penv nenv c
      -- label <- lookupLLVMEnumEnv mc c'
      -- renv <- gets revCaseEnv
      -- p "revcaseenv-insert:"
      -- p' (c', label)
      -- modify (\env -> env {revCaseEnv = Map.insert c' label renv})
      (xts', body') <- discernBinder nenv xts body
      return (((mc, c'), xts'), body')
  return (m, WeakTermCase indName e' cxtes')
discern'' nenv (m, WeakTermQuestion e t) = do
  e' <- discern'' nenv e
  t' <- discern'' nenv t
  return (m, WeakTermQuestion e' t')
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
  removeFromIntactSet mx $ asText x'
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
  insertIntoIntactSet m s
  return x

insertConstant :: Meta -> T.Text -> WithEnv ()
insertConstant m x = do
  cset <- gets constantSet
  if S.member x cset
    then raiseError m $ "the constant `" <> x <> "` is already defined"
    else do
      modify (\env -> env {constantSet = S.insert x (constantSet env)})
      insertIntoIntactSet m x

insertName :: Identifier -> Identifier -> NameEnv -> NameEnv
insertName (I (s, _)) y nenv = Map.insert s y nenv

insertIntoIntactSet :: Meta -> T.Text -> WithEnv ()
insertIntoIntactSet m x =
  whenCheck $ modify (\env -> env {intactSet = S.insert (m, x) (intactSet env)})

removeFromIntactSet :: Meta -> T.Text -> WithEnv ()
removeFromIntactSet m x =
  whenCheck $ modify (\env -> env {intactSet = S.delete (m, x) (intactSet env)})

lookupName ::
     Meta -> [T.Text] -> NameEnv -> Identifier -> WithEnv (Maybe Identifier)
lookupName m penv nenv x =
  case Map.lookup (asText x) nenv of
    Just x' -> do
      removeFromIntactSet m $ asText x'
      return $ Just x'
    Nothing -> lookupName' m penv nenv x

lookupName' ::
     Meta -> [T.Text] -> NameEnv -> Identifier -> WithEnv (Maybe Identifier)
lookupName' _ [] _ _ = return Nothing
lookupName' m (prefix:prefixList) nenv x = do
  let query = prefix <> ":" <> asText x
  case Map.lookup query nenv of
    Just x' -> do
      removeFromIntactSet m query
      return $ Just x'
    Nothing -> lookupName' m prefixList nenv x

lookupName'' :: Meta -> [T.Text] -> NameEnv -> Identifier -> WithEnv Identifier
lookupName'' m penv nenv x = do
  mx <- lookupName m penv nenv x
  case mx of
    Just x' -> return x'
    Nothing -> raiseError m $ "(double-prime) undefined variable: " <> asText x

lookupConstantMaybe :: Meta -> [T.Text] -> T.Text -> WithEnv (Maybe T.Text)
lookupConstantMaybe m penv x = do
  b <- isConstant x
  if b
    then do
      removeFromIntactSet m x
      return $ Just x
    else lookupConstantMaybe' m penv x

lookupConstantMaybe' :: Meta -> [T.Text] -> T.Text -> WithEnv (Maybe T.Text)
lookupConstantMaybe' _ [] _ = return Nothing
lookupConstantMaybe' m (prefix:prefixList) x = do
  let query = prefix <> ":" <> x
  b <- isConstant query
  if b
    then do
      removeFromIntactSet m query
      return $ Just query
    else lookupConstantMaybe' m prefixList x

lookupConstant :: Meta -> [T.Text] -> T.Text -> WithEnv T.Text
lookupConstant m penv x = do
  mc <- lookupConstantMaybe m penv x
  case mc of
    Just c -> return c
    Nothing -> raiseError m $ "undefined constant: " <> x

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
