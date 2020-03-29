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
  x' <- newDefinedNameWith' m nenv x
  e' <- discern'' nenv e
  ss' <- discern' (insertName x x' nenv) ss
  return $ QuasiStmtLet m (mx, x', t') e' : ss'
discern' nenv ((QuasiStmtLetWT m (mx, x, t) e):ss) = do
  t' <- discern'' nenv t
  x' <- newDefinedNameWith' m nenv x
  e' <- discern'' nenv e
  ss' <- discern' (insertName x x' nenv) ss
  return $ QuasiStmtLetWT m (mx, x', t') e' : ss'
discern' nenv (QuasiStmtLetSigma m xts e:ss) = do
  e' <- discern'' nenv e
  (xts', ss') <- discernStmtBinder nenv xts ss
  return $ QuasiStmtLetSigma m xts' e' : ss'
discern' nenv ((QuasiStmtDef xds):ss) = do
  let (xs, ds) = unzip xds
  -- discern for deflist
  let mys = map (\(_, (my, y, _), _, _) -> (my, y)) ds
  ys' <- mapM (\(my, y) -> newDefinedNameWith' my nenv y) mys
  let yis = map (asText . snd) mys
  let nenvForDef = Map.fromList (zip yis ys') `Map.union` nenv
  ds' <- mapM (discernDef nenvForDef) ds
  -- discern for continuation
  xs' <- mapM newDefinedNameWith xs
  let xis = map asText xs
  let nenvForCont = Map.fromList (zip xis xs') `Map.union` nenv
  ss' <- discern' nenvForCont ss
  return $ QuasiStmtDef (zip xs' ds') : ss'
discern' nenv ((QuasiStmtConstDecl m (mx, x, t)):ss) = do
  t' <- discern'' nenv t
  ss' <- discern' nenv ss
  return $ QuasiStmtConstDecl m (mx, x, t') : ss'
discern' nenv ((QuasiStmtImplicit m x i):ss) = do
  penv <- gets prefixEnv
  x' <-
    do mc <- lookupConstantMaybe m penv (asText x)
       case mc of
         Just c -> return c
         Nothing -> lookupNameWithPrefix'' m penv x nenv
  ienv <- gets introEnv
  when (S.member (asInt x') ienv) $ do
    raiseError m $
      "modifying implicit attribute of a constructor `" <>
      asText x' <> "` is prohibited"
  ss' <- discern' nenv ss
  return $ QuasiStmtImplicit m x' i : ss'
discern' nenv ((QuasiStmtImplicitPlus m x i):ss) = do
  penv <- gets prefixEnv
  x' <-
    do mc <- lookupConstantMaybe m penv (asText x)
       case mc of
         Just c -> return c
         Nothing -> lookupNameWithPrefix'' m penv x nenv
  ss' <- discern' nenv ss
  return $ QuasiStmtImplicitPlus m x' i : ss'
discern' nenv ((QuasiStmtEnum m name xis):ss) = do
  insEnumEnv m name xis
  discern' nenv ss
discern' nenv ((QuasiStmtLetInductive n m (mx, a, t) e):ss) = do
  t' <- discern'' nenv t
  a' <- newDefinedNameWith' m nenv a
  e' <- discern'' nenv e
  ss' <- discern' (insertName a a' nenv) ss
  return $ QuasiStmtLetInductive n m (mx, a', t') e' : ss'
-- discern' nenv ((QuasiStmtLetCoinductive n m (mx, a, t) e):ss) = do
--   t' <- discern'' nenv t
--   a' <- newDefinedNameWith' m nenv a
--   e' <- discern'' nenv e
--   ss' <- discern' (insertName a a' nenv) ss
--   return $ QuasiStmtLetCoinductive n m (mx, a', t') e' : ss'
discern' nenv ((QuasiStmtLetInductiveIntro2 m (mx, x, t) e as):ss) = do
  t' <- discern'' nenv t
  x' <- newDefinedNameWith' m nenv x
  e' <- discern'' nenv e
  ss' <- discern' (insertName x x' nenv) ss
  as' <- mapM (lookupStrict'' m nenv) as
  return $ QuasiStmtLetInductiveIntro2 m (mx, x', t') e' as' : ss'
-- discern' nenv ((QuasiStmtLetInductiveIntro m enumInfo (mb, b, t) xts yts ats bts bInner _ _):ss) = do
--   t' <- discern'' nenv t
--   (xts', nenv') <- discernArgs nenv xts
--   (yts', nenv'') <- discernArgs nenv' yts
--   (ats', nenv''') <- discernArgs nenv'' ats
--   (bts', nenv'''') <- discernArgs nenv''' bts
--   bInner' <- discern'' nenv'''' bInner
--   b' <- newDefinedNameWith' m nenv b
--   modify (\env -> env {introEnv = S.insert (asInt b') (introEnv env)})
--   ss' <- discern' (insertName b b' nenv) ss
--   asOuter <- mapM (lookupStrict nenv) ats
--   asInnerPlus <- mapM (lookupStrict' nenv'''') ats
--   let info = zip asOuter asInnerPlus
--   return $
--     QuasiStmtLetInductiveIntro
--       m
--       enumInfo
--       (mb, b', t')
--       xts'
--       yts'
--       ats'
--       bts'
--       bInner'
--       info
--       asOuter :
--     ss'
-- discern' nenv ((QuasiStmtLetCoinductiveElim m (mb, b, t) xtsyt codInner ats bts yt e1 e2 _ _):ss) = do
--   t' <- discern'' nenv t
--   (xtsyt', nenv') <- discernArgs nenv xtsyt
--   e1' <- discern'' nenv' e1
--   (ats', nenv'') <- discernArgs nenv' ats
--   (bts', nenv''') <- discernArgs nenv'' bts
--   (yt', nenv'''') <- discernIdentPlus' nenv''' yt
--   codInner' <- discern'' nenv'''' codInner
--   e2' <- discern'' nenv'''' e2
--   b' <- newDefinedNameWith' m nenv b
--   ss' <- discern' (insertName b b' nenv) ss
--   asOuterPlus <- mapM (lookupStrict' nenv) ats
--   asOuter <- mapM (lookupStrict nenv) ats
--   asInner <- mapM (lookupStrict nenv'''') ats
--   let info = zip asInner asOuterPlus
--   return $
--     QuasiStmtLetCoinductiveElim
--       m
--       (mb, b', t')
--       xtsyt'
--       codInner'
--       ats'
--       bts'
--       yt'
--       e1'
--       e2'
--       info
--       asOuter :
--     ss'
discern' nenv ((QuasiStmtUse prefix):ss) = do
  modify (\e -> e {prefixEnv = prefix : prefixEnv e})
  discern' nenv ss
discern' nenv ((QuasiStmtUnuse prefix):ss) = do
  modify (\e -> e {prefixEnv = filter (/= prefix) (prefixEnv e)})
  discern' nenv ss

discernStmtBinder ::
     NameEnv
  -> [IdentifierPlus]
  -> [QuasiStmt]
  -> WithEnv ([IdentifierPlus], [QuasiStmt])
discernStmtBinder nenv [] ss = do
  ss' <- discern' nenv ss
  return ([], ss')
discernStmtBinder nenv ((mx, x, t):xts) ss = do
  t' <- discern'' nenv t
  x' <- newDefinedNameWith x
  (xts', ss') <- discernStmtBinder (insertName x x' nenv) xts ss
  return ((mx, x', t') : xts', ss')

discernDef :: NameEnv -> Def -> WithEnv Def
discernDef nenv (m, (mx, x, t), xts, e) = do
  t' <- discern'' nenv t
  (xts', e') <- discernBinder nenv xts e
  penv <- gets prefixEnv
  x' <- lookupNameWithPrefix'' mx penv x nenv
  return (m, (mx, x', t'), xts', e')

-- Alpha-convert all the variables so that different variables have different names.
discern'' :: NameEnv -> WeakTermPlus -> WithEnv WeakTermPlus
discern'' _ (m, WeakTermTau l) = return (m, WeakTermTau l)
discern'' nenv (m, WeakTermUpsilon x@(I (s, _))) = do
  penv <- gets prefixEnv
  mx <- lookupNameWithPrefix penv x nenv
  b1 <- lookupEnumValueNameWithPrefix penv s
  b2 <- lookupEnumTypeNameWithPrefix penv s
  mc <- lookupConstantMaybe m penv s
  case (mx, b1, b2, mc) of
    (Just x', _, _, _) -> return (m, WeakTermUpsilon x')
    (_, Just s', _, _) -> return (m, WeakTermEnumIntro (EnumValueLabel s'))
    (_, _, Just s', _) -> return (m, WeakTermEnum (EnumTypeLabel s'))
    (_, _, _, Just c) -> return (m, WeakTermConst c emptyUP)
    _ -> raiseError m $ "undefined variable:  " <> asText x
discern'' nenv (m, WeakTermPi mls xts t) = do
  (xts', t') <- discernBinder nenv xts t
  return (m, WeakTermPi mls xts' t')
discern'' nenv (m, WeakTermPiPlus name mls xts t) = do
  (xts', t') <- discernBinder nenv xts t
  return (m, WeakTermPiPlus name mls xts' t')
discern'' nenv (m, WeakTermPiIntro xts e) = do
  (xts', e') <- discernBinder nenv xts e
  return (m, WeakTermPiIntro xts' e')
discern'' nenv (m, WeakTermPiIntroNoReduce xts e) = do
  (xts', e') <- discernBinder nenv xts e
  return (m, WeakTermPiIntroNoReduce xts' e')
discern'' nenv (m, WeakTermPiIntroPlus ind (name, args1, args2) xts e) = do
  undefined
  -- args' <- mapM (discernIdentPlus nenv) args -- ところでこれは前のargsに後ろのargsが依存できないから間違いですね
  -- (xts', e') <- discernBinder nenv xts e
  -- return (m, WeakTermPiIntroPlus ind (name, args') xts' e')
discern'' nenv (m, WeakTermPiElim e es) = do
  es' <- mapM (discern'' nenv) es
  e' <- discern'' nenv e
  return (m, WeakTermPiElim e' es')
discern'' nenv (m, WeakTermSigma xts) = do
  xts' <- discernSigma nenv xts
  return (m, WeakTermSigma xts')
discern'' nenv (m, WeakTermSigmaIntro t es) = do
  t' <- discern'' nenv t
  es' <- mapM (discern'' nenv) es
  return (m, WeakTermSigmaIntro t' es')
discern'' nenv (m, WeakTermSigmaElim t xts e1 e2) = do
  t' <- discern'' nenv t
  e1' <- discern'' nenv e1
  (xts', e2') <- discernBinder nenv xts e2
  return (m, WeakTermSigmaElim t' xts' e1' e2')
discern'' nenv (m, WeakTermIter xt xts e) = do
  (xt', xts', e') <- discernIter nenv xt xts e
  return (m, WeakTermIter xt' xts' e')
discern'' _ (m, WeakTermConst x up) = return (m, WeakTermConst x up)
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
  caseList' <- discernCaseList nenv caseList
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
discern'' nenv (m, WeakTermCase (e, t) cxtes) = do
  e' <- discern'' nenv e
  t' <- discern'' nenv t
  penv <- gets prefixEnv
  cxtes' <-
    flip mapM cxtes $ \(((mc, c), xts), body) -> do
      (expandedName, c') <- lookupConsNameWithPrefix mc penv c nenv
      label <- lookupLLVMEnumEnv mc expandedName
      renv <- gets revCaseEnv
      modify (\env -> env {revCaseEnv = IntMap.insert (asInt c') label renv})
      (xts', body') <- discernBinder nenv xts body
      return (((mc, c'), xts'), body')
  return (m, WeakTermCase (e', t') cxtes')

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
  x' <- newDefinedNameWith x
  (xts', e') <- discernBinder (insertName x x' nenv) xts e
  return ((mx, x', t') : xts', e')

discernSigma :: NameEnv -> [IdentifierPlus] -> WithEnv [IdentifierPlus]
discernSigma _ [] = return []
discernSigma nenv ((mx, x, t):xts) = do
  t' <- discern'' nenv t
  x' <- newDefinedNameWith x
  xts' <- discernSigma (insertName x x' nenv) xts
  return $ (mx, x', t') : xts'

-- discernArgs ::
--      NameEnv -> [IdentifierPlus] -> WithEnv ([IdentifierPlus], NameEnv)
-- discernArgs nenv [] = return ([], nenv)
-- discernArgs nenv ((mx, x, t):xts) = do
--   t' <- discern'' nenv t
--   x' <- newDefinedNameWith x
--   (xts', nenv') <- discernArgs (insertName x x' nenv) xts
--   return ((mx, x', t') : xts', nenv')
discernIdentPlus :: NameEnv -> IdentifierPlus -> WithEnv IdentifierPlus
discernIdentPlus nenv (m, x, t) = do
  t' <- discern'' nenv t
  penv <- gets prefixEnv
  x' <- lookupNameWithPrefix'' m penv x nenv
  return (m, x', t')

-- discernIdentPlus' ::
--      NameEnv -> IdentifierPlus -> WithEnv (IdentifierPlus, NameEnv)
-- discernIdentPlus' nenv (m, x, t) = do
--   t' <- discern'' nenv t
--   x' <- newDefinedNameWith x
--   return ((m, x', t'), insertName x x' nenv)
discernIter ::
     NameEnv
  -> IdentifierPlus
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> WithEnv (IdentifierPlus, [IdentifierPlus], WeakTermPlus)
discernIter nenv (mx, x, t) xts e = do
  t' <- discern'' nenv t
  discernIter' nenv (mx, x, t') xts e

discernIter' ::
     NameEnv
  -> IdentifierPlus
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> WithEnv (IdentifierPlus, [IdentifierPlus], WeakTermPlus)
discernIter' nenv (mx, x, t') [] e = do
  x' <- newDefinedNameWith x
  e' <- discern'' (insertName x x' nenv) e
  return ((mx, x', t'), [], e')
discernIter' nenv xt ((mx, x, t):xts) e = do
  t' <- discern'' nenv t
  x' <- newDefinedNameWith x
  (xt', xts', e') <- discernIter' (insertName x x' nenv) xt xts e
  return (xt', (mx, x', t') : xts', e')

discernCaseList ::
     NameEnv
  -> [(WeakCasePlus, WeakTermPlus)]
  -> WithEnv [(WeakCasePlus, WeakTermPlus)]
discernCaseList nenv caseList =
  forM caseList $ \((mCase, l), body) -> do
    l' <- discernWeakCase mCase nenv l
    body' <- discern'' nenv body
    return ((mCase, l'), body')

discernWeakCase :: Meta -> NameEnv -> WeakCase -> WithEnv WeakCase
discernWeakCase _ nenv (WeakCaseInt t a) = do
  t' <- discern'' nenv t
  return (WeakCaseInt t' a)
discernWeakCase m _ (WeakCaseLabel l) = do
  penv <- gets prefixEnv
  ml <- lookupEnumValueNameWithPrefix penv l
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
  x' <- newDefinedNameWith x
  (xts', e') <- discernStruct (insertName x x' nenv) xts e
  return ((mx, x', t) : xts', e')

newDefinedNameWith :: Identifier -> WithEnv Identifier
newDefinedNameWith (I (s, _)) = do
  j <- newCount
  modify (\e -> e {nameEnv = Map.insert s s (nameEnv e)})
  return $ I (s, j)

newDefinedNameWith' :: Meta -> NameEnv -> Identifier -> WithEnv Identifier
newDefinedNameWith' m nenv x = do
  case Map.lookup (asText x) nenv of
    Nothing -> newDefinedNameWith x
    Just _ ->
      raiseError m $
      "the identifier `" <> asText x <> "` is already defined at top level"

-- lookupStrict :: NameEnv -> IdentifierPlus -> WithEnv Identifier
-- lookupStrict nenv (m, x, _) = do
--   penv <- gets prefixEnv
--   lookupNameWithPrefix'' m penv x nenv
-- lookupStrict' :: NameEnv -> IdentifierPlus -> WithEnv WeakTermPlus
-- lookupStrict' nenv xt@(m, _, _) = do
--   x' <- lookupStrict nenv xt
--   return (m, WeakTermUpsilon x')
lookupStrict'' :: Meta -> NameEnv -> Identifier -> WithEnv Identifier
lookupStrict'' m nenv x = do
  penv <- gets prefixEnv
  lookupNameWithPrefix'' m penv x nenv

insertName :: Identifier -> Identifier -> NameEnv -> NameEnv
insertName (I (s, _)) y nenv = Map.insert s y nenv

lookupNameWithPrefix ::
     [T.Text] -> Identifier -> NameEnv -> WithEnv (Maybe Identifier)
lookupNameWithPrefix penv x nenv =
  case Map.lookup (asText x) nenv of
    Just x' -> return $ Just x'
    Nothing -> lookupNameWithPrefix' penv x nenv

lookupNameWithPrefix' ::
     [T.Text] -> Identifier -> NameEnv -> WithEnv (Maybe Identifier)
lookupNameWithPrefix' [] _ _ = return Nothing
lookupNameWithPrefix' (prefix:prefixList) x nenv =
  case Map.lookup (prefix <> ":" <> asText x) nenv of
    Just x' -> return $ Just x'
    Nothing -> lookupNameWithPrefix' prefixList x nenv

lookupNameWithPrefix'' ::
     Meta -> [T.Text] -> Identifier -> NameEnv -> WithEnv Identifier
lookupNameWithPrefix'' m penv x nenv = do
  mx <- lookupNameWithPrefix penv x nenv
  case mx of
    Just x' -> return x'
    Nothing -> raiseError m $ "undefined variable: " <> asText x

lookupConsNameWithPrefix ::
     Meta -> [T.Text] -> Identifier -> NameEnv -> WithEnv (T.Text, Identifier)
lookupConsNameWithPrefix m penv x nenv =
  case Map.lookup (asText x) nenv of
    Just x' -> return (asText x, x')
    Nothing -> lookupConsNameWithPrefix' m penv x nenv

lookupConsNameWithPrefix' ::
     Meta -> [T.Text] -> Identifier -> NameEnv -> WithEnv (T.Text, Identifier)
lookupConsNameWithPrefix' m [] x _ =
  raiseError m $ "undefined variable: " <> asText x
lookupConsNameWithPrefix' m (prefix:prefixList) x nenv = do
  let query = prefix <> ":" <> asText x
  case Map.lookup query nenv of
    Just x' -> return (query, x')
    Nothing -> lookupConsNameWithPrefix' m prefixList x nenv

lookupEnumValueNameWithPrefix :: [T.Text] -> T.Text -> WithEnv (Maybe T.Text)
lookupEnumValueNameWithPrefix penv name = do
  b <- isDefinedEnumValue name
  if b
    then return $ Just name
    else lookupEnumValueNameWithPrefix' penv name

lookupEnumValueNameWithPrefix' :: [T.Text] -> T.Text -> WithEnv (Maybe T.Text)
lookupEnumValueNameWithPrefix' [] _ = return Nothing
lookupEnumValueNameWithPrefix' (prefix:prefixList) name = do
  let name' = prefix <> ":" <> name
  b <- isDefinedEnumValue name'
  if b
    then return $ Just name'
    else lookupEnumValueNameWithPrefix' prefixList name

isDefinedEnumValue :: T.Text -> WithEnv Bool
isDefinedEnumValue name = do
  env <- get
  let labelList = join $ Map.elems $ enumEnv env
  return $ name `elem` map fst labelList

lookupEnumTypeNameWithPrefix :: [T.Text] -> T.Text -> WithEnv (Maybe T.Text)
lookupEnumTypeNameWithPrefix penv name = do
  b <- isDefinedEnumType name
  if b
    then return $ Just name
    else lookupEnumTypeNameWithPrefix' penv name

lookupEnumTypeNameWithPrefix' :: [T.Text] -> T.Text -> WithEnv (Maybe T.Text)
lookupEnumTypeNameWithPrefix' [] _ = return Nothing
lookupEnumTypeNameWithPrefix' (prefix:prefixList) name = do
  let name' = prefix <> ":" <> name
  b <- isDefinedEnumType name'
  if b
    then return $ Just name'
    else lookupEnumTypeNameWithPrefix' prefixList name

isDefinedEnumType :: T.Text -> WithEnv Bool
isDefinedEnumType name = do
  env <- get
  let enumNameList = Map.keys $ enumEnv env
  return $ name `elem` enumNameList
