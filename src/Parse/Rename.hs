{-# LANGUAGE OverloadedStrings #-}

module Parse.Rename
  ( rename
  , renameQuasiStmtList
  , insertName
  , rename'
  , NameEnv
  , unravel
  ) where

import Control.Monad.Except
import Control.Monad.State

import qualified Data.HashMap.Strict as Map
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Text as T

import Data.Basic
import Data.Env
import Data.WeakTerm

rename :: WeakTermPlus -> WithEnv WeakTermPlus
rename e = rename' Map.empty e

renameQuasiStmtList :: [QuasiStmt] -> WithEnv [QuasiStmt]
renameQuasiStmtList = renameQuasiStmtList' Map.empty

renameQuasiStmtList' :: NameEnv -> [QuasiStmt] -> WithEnv [QuasiStmt]
renameQuasiStmtList' _ [] = return []
renameQuasiStmtList' nenv ((QuasiStmtLet m (mx, x, t) e):ss) = do
  t' <- rename' nenv t
  x' <- newLLVMNameWithStrict m nenv x
  e' <- rename' nenv e
  ss' <- renameQuasiStmtList' (insertName x x' nenv) ss
  return $ QuasiStmtLet m (mx, x', t') e' : ss'
renameQuasiStmtList' nenv ((QuasiStmtLetWT m (mx, x, t) e):ss) = do
  t' <- rename' nenv t
  x' <- newLLVMNameWithStrict m nenv x
  e' <- rename' nenv e
  ss' <- renameQuasiStmtList' (insertName x x' nenv) ss
  return $ QuasiStmtLetWT m (mx, x', t') e' : ss'
renameQuasiStmtList' nenv (QuasiStmtLetSigma m xts e:ss) = do
  e' <- rename' nenv e
  (xts', ss') <- renameStmtBinder nenv xts ss
  return $ QuasiStmtLetSigma m xts' e' : ss'
renameQuasiStmtList' nenv ((QuasiStmtDef xds):ss) = do
  let (xs, ds) = unzip xds
  -- rename for deflist
  let mys = map (\(_, (my, y, _), _, _) -> (my, y)) ds
  ys' <- mapM (\(my, y) -> newLLVMNameWithStrict my nenv y) mys
  let yis = map (asText . snd) mys
  let yis' = map asInt ys'
  let nenvForDef = Map.fromList (zip yis yis') `Map.union` nenv
  ds' <- mapM (renameDef nenvForDef) ds
  -- rename for continuation
  xs' <- mapM newLLVMNameWith xs
  let xis = map asText xs
  let xis' = map asInt xs'
  let nenvForCont = Map.fromList (zip xis xis') `Map.union` nenv
  ss' <- renameQuasiStmtList' nenvForCont ss
  return $ QuasiStmtDef (zip xs' ds') : ss'
renameQuasiStmtList' nenv ((QuasiStmtConstDecl m (mx, x, t)):ss) = do
  t' <- rename' nenv t
  ss' <- renameQuasiStmtList' nenv ss
  return $ QuasiStmtConstDecl m (mx, x, t') : ss'
renameQuasiStmtList' nenv ((QuasiStmtImplicit m x i):ss) = do
  cenv <- gets constantEnv
  x' <-
    case Map.lookup (asText x) cenv of
      Just j -> return $ I (asText x, j)
      Nothing -> renameIdentifier nenv m x
  ss' <- renameQuasiStmtList' nenv ss
  return $ QuasiStmtImplicit m x' i : ss'
renameQuasiStmtList' nenv ((QuasiStmtLetInductive n m (mx, a, t) e):ss) = do
  t' <- rename' nenv t
  a' <- newLLVMNameWithStrict m nenv a
  e' <- rename' nenv e
  ss' <- renameQuasiStmtList' (insertName a a' nenv) ss
  return $ QuasiStmtLetInductive n m (mx, a', t') e' : ss'
renameQuasiStmtList' nenv ((QuasiStmtLetCoinductive n m (mx, a, t) e):ss) = do
  t' <- rename' nenv t
  a' <- newLLVMNameWithStrict m nenv a
  e' <- rename' nenv e
  ss' <- renameQuasiStmtList' (insertName a a' nenv) ss
  return $ QuasiStmtLetCoinductive n m (mx, a', t') e' : ss'
renameQuasiStmtList' nenv ((QuasiStmtLetInductiveIntro m enumInfo (mb, b, t) xts yts ats bts bInner _ _):ss) = do
  t' <- rename' nenv t
  (xts', nenv') <- renameArgs nenv xts
  (yts', nenv'') <- renameArgs nenv' yts
  (ats', nenv''') <- renameArgs nenv'' ats
  (bts', nenv'''') <- renameArgs nenv''' bts
  bInner' <- rename' nenv'''' bInner
  b' <- newLLVMNameWithStrict m nenv b
  ss' <- renameQuasiStmtList' (insertName b b' nenv) ss
  asOuter <- mapM (lookupStrict nenv) ats
  asInnerPlus <- mapM (lookupStrict' nenv'''') ats
  let info = zip asOuter asInnerPlus
  return $
    QuasiStmtLetInductiveIntro
      m
      enumInfo
      (mb, b', t')
      xts'
      yts'
      ats'
      bts'
      bInner'
      info
      asOuter :
    ss'
renameQuasiStmtList' nenv ((QuasiStmtLetCoinductiveElim m (mb, b, t) xtsyt codInner ats bts yt e1 e2 _ _):ss) = do
  t' <- rename' nenv t
  (xtsyt', nenv') <- renameArgs nenv xtsyt
  e1' <- rename' nenv' e1
  (ats', nenv'') <- renameArgs nenv' ats
  (bts', nenv''') <- renameArgs nenv'' bts
  (yt', nenv'''') <- renameIdentPlus' nenv''' yt
  codInner' <- rename' nenv'''' codInner
  e2' <- rename' nenv'''' e2
  b' <- newLLVMNameWithStrict m nenv b
  ss' <- renameQuasiStmtList' (insertName b b' nenv) ss
  asOuterPlus <- mapM (lookupStrict' nenv) ats
  asOuter <- mapM (lookupStrict nenv) ats
  asInner <- mapM (lookupStrict nenv'''') ats
  let info = zip asInner asOuterPlus
  return $
    QuasiStmtLetCoinductiveElim
      m
      (mb, b', t')
      xtsyt'
      codInner'
      ats'
      bts'
      yt'
      e1'
      e2'
      info
      asOuter :
    ss'

newLLVMNameWithStrict :: Meta -> NameEnv -> Identifier -> WithEnv Identifier
newLLVMNameWithStrict m nenv x = do
  case Map.lookup (asText x) nenv of
    Nothing -> newLLVMNameWith x
    Just _ ->
      raiseError m $
      "the identifier `" <> asText x <> "` is already defined at top level"

renameStmtBinder ::
     NameEnv
  -> [IdentifierPlus]
  -> [QuasiStmt]
  -> WithEnv ([IdentifierPlus], [QuasiStmt])
renameStmtBinder nenv [] ss = do
  ss' <- renameQuasiStmtList' nenv ss
  return ([], ss')
renameStmtBinder nenv ((mx, x, t):xts) ss = do
  t' <- rename' nenv t
  x' <- newLLVMNameWith x
  (xts', ss') <- renameStmtBinder (insertName x x' nenv) xts ss
  return ((mx, x', t') : xts', ss')

renameDef :: NameEnv -> Def -> WithEnv Def
renameDef nenv (m, (mx, x, t), xts, e) = do
  t' <- rename' nenv t
  (xts', e') <- renameBinder nenv xts e
  case lookupName x nenv of
    Nothing -> raiseError mx $ "undefined variable: " <> asText x
    Just x' -> return (m, (mx, x', t'), xts', e')

type NameEnv = Map.HashMap T.Text Int

-- Alpha-convert all the variables so that different variables have different names.
rename' :: NameEnv -> WeakTermPlus -> WithEnv WeakTermPlus
rename' _ (m, WeakTermTau l) = return (m, WeakTermTau l)
rename' nenv (m, WeakTermUpsilon x@(I (s, _))) = do
  b1 <- isDefinedEnumValue s
  b2 <- isDefinedEnumType s
  mc <- lookupConstantMaybe m s
  case (lookupName x nenv, b1, b2, mc) of
    (Just x', _, _, _) -> return (m, WeakTermUpsilon x')
    (_, True, _, _) -> return (m, WeakTermEnumIntro (EnumValueLabel s))
    (_, _, True, _) -> return (m, WeakTermEnum (EnumTypeLabel s))
    (_, _, _, Just c) -> return c
    _ -> raiseError m $ "undefined variable: " <> s
rename' nenv (m, WeakTermPi mls xts t) = do
  (xts', t') <- renameBinder nenv xts t
  return (m, WeakTermPi mls xts' t')
rename' nenv (m, WeakTermPiPlus name mls xts t) = do
  (xts', t') <- renameBinder nenv xts t
  return (m, WeakTermPiPlus name mls xts' t')
rename' nenv (m, WeakTermPiIntro xts e) = do
  (xts', e') <- renameBinder nenv xts e
  return (m, WeakTermPiIntro xts' e')
rename' nenv (m, WeakTermPiIntroNoReduce xts e) = do
  (xts', e') <- renameBinder nenv xts e
  return (m, WeakTermPiIntroNoReduce xts' e')
rename' nenv (m, WeakTermPiIntroPlus ind (name, args) xts e) = do
  args' <- mapM (renameIdentPlus nenv) args
  (xts', e') <- renameBinder nenv xts e
  return (m, WeakTermPiIntroPlus ind (name, args') xts' e')
rename' nenv (m, WeakTermPiElim e es) = do
  es' <- mapM (rename' nenv) es
  e' <- rename' nenv e
  return (m, WeakTermPiElim e' es')
rename' nenv (m, WeakTermSigma xts) = do
  xts' <- renameSigma nenv xts
  return (m, WeakTermSigma xts')
rename' nenv (m, WeakTermSigmaIntro t es) = do
  t' <- rename' nenv t
  es' <- mapM (rename' nenv) es
  return (m, WeakTermSigmaIntro t' es')
rename' nenv (m, WeakTermSigmaElim t xts e1 e2) = do
  t' <- rename' nenv t
  e1' <- rename' nenv e1
  (xts', e2') <- renameBinder nenv xts e2
  return (m, WeakTermSigmaElim t' xts' e1' e2')
rename' nenv (m, WeakTermIter xt xts e) = do
  (xt', xts', e') <- renameIter nenv xt xts e
  return (m, WeakTermIter xt' xts' e')
rename' _ (m, WeakTermConst x) = return (m, WeakTermConst x)
rename' _ (m, WeakTermZeta h) = do
  return (m, WeakTermZeta h)
rename' _ (m, WeakTermInt t x) = do
  t' <- rename t
  return (m, WeakTermInt t' x)
rename' _ (m, WeakTermFloat16 x) = return (m, WeakTermFloat16 x)
rename' _ (m, WeakTermFloat32 x) = return (m, WeakTermFloat32 x)
rename' _ (m, WeakTermFloat64 x) = return (m, WeakTermFloat64 x)
rename' nenv (m, WeakTermFloat t x) = do
  t' <- rename' nenv t
  return (m, WeakTermFloat t' x)
rename' _ (m, WeakTermEnum s) = return (m, WeakTermEnum s)
rename' _ (m, WeakTermEnumIntro x) = return (m, WeakTermEnumIntro x)
rename' nenv (m, WeakTermEnumElim (e, t) caseList) = do
  e' <- rename' nenv e
  t' <- rename' nenv t
  caseList' <- renameCaseList nenv caseList
  return (m, WeakTermEnumElim (e', t') caseList')
rename' nenv (m, WeakTermArray dom kind) = do
  dom' <- rename' nenv dom
  return (m, WeakTermArray dom' kind)
rename' nenv (m, WeakTermArrayIntro kind es) = do
  es' <- mapM (rename' nenv) es
  return (m, WeakTermArrayIntro kind es')
rename' nenv (m, WeakTermArrayElim kind xts e1 e2) = do
  e1' <- rename' nenv e1
  (xts', e2') <- renameBinder nenv xts e2
  return (m, WeakTermArrayElim kind xts' e1' e2')
rename' _ (m, WeakTermStruct ts) = return (m, WeakTermStruct ts)
rename' nenv (m, WeakTermStructIntro ets) = do
  let (es, ts) = unzip ets
  es' <- mapM (rename' nenv) es
  return (m, WeakTermStructIntro $ zip es' ts)
rename' nenv (m, WeakTermStructElim xts e1 e2) = do
  e1' <- rename' nenv e1
  (xts', e2') <- renameStruct nenv xts e2
  return (m, WeakTermStructElim xts' e1' e2')
rename' nenv (m, WeakTermCase (e, t) cxtes) = do
  e' <- rename' nenv e
  t' <- rename' nenv t
  cxtes' <-
    flip mapM cxtes $ \((c, xts), body) -> do
      c' <- lookupStrict'' nenv m c
      (xts', body') <- renameBinder nenv xts body
      return ((c', xts'), body')
  return (m, WeakTermCase (e', t') cxtes')

renameBinder ::
     NameEnv
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> WithEnv ([IdentifierPlus], WeakTermPlus)
renameBinder nenv [] e = do
  e' <- rename' nenv e
  return ([], e')
renameBinder nenv ((mx, x, t):xts) e = do
  t' <- rename' nenv t
  x' <- newLLVMNameWith x
  (xts', e') <- renameBinder (insertName x x' nenv) xts e
  return ((mx, x', t') : xts', e')

renameSigma :: NameEnv -> [IdentifierPlus] -> WithEnv [IdentifierPlus]
renameSigma _ [] = return []
renameSigma nenv ((mx, x, t):xts) = do
  t' <- rename' nenv t
  x' <- newLLVMNameWith x
  xts' <- renameSigma (insertName x x' nenv) xts
  return $ (mx, x', t') : xts'

renameArgs :: NameEnv -> [IdentifierPlus] -> WithEnv ([IdentifierPlus], NameEnv)
renameArgs nenv [] = return ([], nenv)
renameArgs nenv ((mx, x, t):xts) = do
  t' <- rename' nenv t
  x' <- newLLVMNameWith x
  (xts', nenv') <- renameArgs (insertName x x' nenv) xts
  return ((mx, x', t') : xts', nenv')

renameIdentifier :: NameEnv -> Meta -> Identifier -> WithEnv Identifier
renameIdentifier nenv m x@(I (s, _)) = do
  case lookupName x nenv of
    Just x' -> return x'
    _ -> raiseError m $ "undefined variable: " <> s

renameIdentPlus :: NameEnv -> IdentifierPlus -> WithEnv IdentifierPlus
renameIdentPlus nenv (m, x, t) = do
  t' <- rename' nenv t
  x' <- renameIdentifier nenv m x
  return (m, x', t')

renameIdentPlus' ::
     NameEnv -> IdentifierPlus -> WithEnv (IdentifierPlus, NameEnv)
renameIdentPlus' nenv (m, x, t) = do
  t' <- rename' nenv t
  x' <- newLLVMNameWith x
  return ((m, x', t'), insertName x x' nenv)

renameIter ::
     NameEnv
  -> IdentifierPlus
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> WithEnv (IdentifierPlus, [IdentifierPlus], WeakTermPlus)
renameIter nenv (mx, x, t) xts e = do
  t' <- rename' nenv t
  renameIter' nenv (mx, x, t') xts e

renameIter' ::
     NameEnv
  -> IdentifierPlus
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> WithEnv (IdentifierPlus, [IdentifierPlus], WeakTermPlus)
renameIter' nenv (mx, x, t') [] e = do
  x' <- newLLVMNameWith x
  e' <- rename' (insertName x x' nenv) e
  return ((mx, x', t'), [], e')
renameIter' nenv xt ((mx, x, t):xts) e = do
  t' <- rename' nenv t
  x' <- newLLVMNameWith x
  (xt', xts', e') <- renameIter' (insertName x x' nenv) xt xts e
  return (xt', (mx, x', t') : xts', e')

renameCaseList ::
     NameEnv -> [(WeakCase, WeakTermPlus)] -> WithEnv [(WeakCase, WeakTermPlus)]
renameCaseList nenv caseList =
  forM caseList $ \(l, body) -> do
    l' <- renameWeakCase nenv l
    body' <- rename' nenv body
    return (l', body')

renameWeakCase :: NameEnv -> WeakCase -> WithEnv WeakCase
renameWeakCase nenv (WeakCaseInt t a) = do
  t' <- rename' nenv t
  return (WeakCaseInt t' a)
renameWeakCase _ l = return l

renameStruct ::
     NameEnv
  -> [(Meta, Identifier, ArrayKind)]
  -> WeakTermPlus
  -> WithEnv ([(Meta, Identifier, ArrayKind)], WeakTermPlus)
renameStruct nenv [] e = do
  e' <- rename' nenv e
  return ([], e')
renameStruct nenv ((mx, x, t):xts) e = do
  x' <- newLLVMNameWith x
  (xts', e') <- renameStruct (insertName x x' nenv) xts e
  return ((mx, x', t) : xts', e')

lookupStrict :: NameEnv -> IdentifierPlus -> WithEnv Identifier
lookupStrict nenv (m, x, _) =
  case lookupName x nenv of
    Just x' -> return x'
    Nothing -> raiseError m $ "undefined variable:  " <> asText x

lookupStrict' :: NameEnv -> IdentifierPlus -> WithEnv WeakTermPlus
lookupStrict' nenv (m, x, _) =
  case lookupName x nenv of
    Just x' -> return (m, WeakTermUpsilon x')
    Nothing -> raiseError m $ "undefined variable:  " <> asText x

lookupStrict'' :: NameEnv -> Meta -> Identifier -> WithEnv Identifier
lookupStrict'' nenv m x =
  case lookupName' x nenv of
    Just x' -> return x'
    Nothing -> raiseError m $ "undefined variable:  " <> asText x

unravel :: WeakTermPlus -> WithEnv WeakTermPlus
unravel (m, WeakTermTau l) = return (m, WeakTermTau l)
unravel (m, WeakTermUpsilon x) = do
  x' <- unravelUpsilon x
  return (m, WeakTermUpsilon x')
unravel (m, WeakTermPi mls xts t) = do
  (xts', t') <- unravelBinder xts t
  return (m, WeakTermPi mls xts' t')
unravel (m, WeakTermPiPlus name mls xts t) = do
  (xts', t') <- unravelBinder xts t
  return (m, WeakTermPiPlus name mls xts' t')
unravel (m, WeakTermPiIntro xts e) = do
  (xts', e') <- unravelBinder xts e
  return (m, WeakTermPiIntro xts' e')
unravel (m, WeakTermPiIntroNoReduce xts e) = do
  (xts', e') <- unravelBinder xts e
  return (m, WeakTermPiIntroNoReduce xts' e')
-- the "content" of this term is not used in toText, and so there's no need to rename this term
unravel (m, WeakTermPiIntroPlus ind (name, args) xts e) =
  return (m, WeakTermPiIntroPlus ind (name, args) xts e)
unravel (m, WeakTermPiElim e es) = do
  e' <- unravel e
  es' <- mapM unravel es
  return (m, WeakTermPiElim e' es')
unravel (m, WeakTermSigma xts) =
  case splitLast xts of
    Nothing -> return (m, WeakTermSigma xts)
    Just (yts, (my, y, t)) -> do
      yts' <- unravelSigma yts
      t' <- unravel t
      return (m, WeakTermSigma $ yts' ++ [(my, y, t')])
unravel (m, WeakTermSigmaIntro t es) = do
  es' <- mapM unravel es
  -- don't rename t since it is not printed
  return (m, WeakTermSigmaIntro t es')
unravel (m, WeakTermSigmaElim t xts e1 e2) = do
  e1' <- unravel e1
  (xts', e2') <- unravelBinder xts e2
  return (m, WeakTermSigmaElim t xts' e1' e2')
unravel (m, WeakTermIter (mx, x, t) xts e) = do
  x' <- unravelUpsilon x
  (xts', e') <- unravelBinder xts e
  return (m, WeakTermIter (mx, x', t) xts' e')
unravel (m, WeakTermConst x) = return (m, WeakTermConst x)
unravel (m, WeakTermZeta h) = do
  h' <- unravelZeta h
  return (m, WeakTermZeta h')
unravel (m, WeakTermInt t x) = do
  return (m, WeakTermInt t x)
unravel (m, WeakTermFloat16 x) = return (m, WeakTermFloat16 x)
unravel (m, WeakTermFloat32 x) = return (m, WeakTermFloat32 x)
unravel (m, WeakTermFloat64 x) = return (m, WeakTermFloat64 x)
unravel (m, WeakTermFloat t x) = do
  return (m, WeakTermFloat t x)
unravel (m, WeakTermEnum s) = return (m, WeakTermEnum s)
unravel (m, WeakTermEnumIntro x) = return (m, WeakTermEnumIntro x)
unravel (m, WeakTermEnumElim (e, t) caseList) = do
  e' <- unravel e
  caseList' <- unravelCaseList caseList
  return (m, WeakTermEnumElim (e', t) caseList')
unravel (m, WeakTermArray dom kind) = do
  dom' <- unravel dom
  return (m, WeakTermArray dom' kind)
unravel (m, WeakTermArrayIntro kind es) = do
  es' <- mapM unravel es
  return (m, WeakTermArrayIntro kind es')
unravel (m, WeakTermArrayElim kind xts e1 e2) = do
  e1' <- unravel e1
  (xts', e2') <- unravelBinder xts e2
  return (m, WeakTermArrayElim kind xts' e1' e2')
unravel (m, WeakTermStruct ts) = return (m, WeakTermStruct ts)
unravel (m, WeakTermStructIntro ets) = do
  let (es, ts) = unzip ets
  es' <- mapM unravel es
  return (m, WeakTermStructIntro $ zip es' ts)
unravel (m, WeakTermStructElim xts e1 e2) = do
  e1' <- unravel e1
  (xts', e2') <- unravelStruct xts e2
  return (m, WeakTermStructElim xts' e1' e2')
unravel (m, WeakTermCase (e, t) cxtes) = do
  e' <- unravel e
  t' <- unravel t
  cxtes' <-
    flip mapM cxtes $ \((c, xts), body) -> do
      (xts', body') <- unravelBinder xts body
      return ((c, xts'), body')
  return (m, WeakTermCase (e', t') cxtes')

unravelUpsilon :: Identifier -> WithEnv Identifier
unravelUpsilon (I (s, i)) = do
  nenv <- gets nameEnv
  case Map.lookup s nenv of
    Just s' -> return $ I (s', i)
    Nothing -> do
      j <- newCount
      let s' = T.pack $ "var" ++ show j
      modify (\e -> e {nameEnv = Map.insert s s' nenv})
      return $ I (s', i)

unravelZeta :: Identifier -> WithEnv Identifier
unravelZeta (I (s, i)) = do
  rnenv <- gets revNameEnv
  case IntMap.lookup i rnenv of
    Just j -> return $ I (s, j)
    Nothing -> do
      j <- newCount
      modify (\env -> env {revNameEnv = IntMap.insert i j rnenv})
      return $ I (s, j)

unravelBinder ::
     [IdentifierPlus]
  -> WeakTermPlus
  -> WithEnv ([IdentifierPlus], WeakTermPlus)
unravelBinder [] e = do
  e' <- unravel e
  return ([], e')
unravelBinder ((mx, x, t):xts) e = do
  t' <- unravel t
  x' <- unravelUpsilon x
  (xts', e') <- unravelBinder xts e
  return ((mx, x', t') : xts', e')

unravelSigma :: [IdentifierPlus] -> WithEnv [IdentifierPlus]
unravelSigma [] = return []
unravelSigma ((mx, x, t):xts) = do
  t' <- unravel t
  x' <- unravelUpsilon x
  xts' <- unravelSigma xts
  return $ (mx, x', t') : xts'

unravelCaseList ::
     [(WeakCase, WeakTermPlus)] -> WithEnv [(WeakCase, WeakTermPlus)]
unravelCaseList caseList = do
  let (ls, es) = unzip caseList
  ls' <- mapM unravelWeakCase ls
  es' <- mapM unravel es
  return $ zip ls' es'

unravelWeakCase :: WeakCase -> WithEnv WeakCase
unravelWeakCase (WeakCaseInt t a) = do
  t' <- unravel t
  return $ WeakCaseInt t' a
unravelWeakCase l = return l

unravelStruct ::
     [(Meta, Identifier, ArrayKind)]
  -> WeakTermPlus
  -> WithEnv ([(Meta, Identifier, ArrayKind)], WeakTermPlus)
unravelStruct [] e = do
  e' <- unravel e
  return ([], e')
unravelStruct ((mx, x, t):xts) e = do
  x' <- unravelUpsilon x
  (xts', e') <- unravelStruct xts e
  return ((mx, x', t) : xts', e')

insertName :: Identifier -> Identifier -> NameEnv -> NameEnv
insertName (I (s, _)) (I (_, j)) nenv = Map.insert s j nenv

lookupName :: Identifier -> NameEnv -> Maybe Identifier
lookupName (I (s, _)) nenv = do
  j <- Map.lookup s nenv
  return $ I (llvmString s, j)

lookupName' :: Identifier -> NameEnv -> Maybe Identifier
lookupName' (I (s, _)) nenv = do
  j <- Map.lookup s nenv
  return $ I (s, j)
