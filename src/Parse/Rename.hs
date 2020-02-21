{-# LANGUAGE OverloadedStrings #-}

module Parse.Rename
  ( rename
  , renameQuasiStmtList
  , insertName
  , rename'
  , NameEnv
  , invRename
  , prepareInvRename
  ) where

import Control.Monad.Except
import Control.Monad.State

import qualified Data.HashMap.Strict as Map
import qualified Data.Text as T

import Data.Basic
import Data.Env
import Data.WeakTerm

rename :: WeakTermPlus -> WithEnv WeakTermPlus
rename e = do
  result <- rename' Map.empty e
  let info = toInfo "rename.post" result
  return $ assertP info result $ checkSanity [] result

renameQuasiStmtList :: [QuasiStmt] -> WithEnv [QuasiStmt]
renameQuasiStmtList = renameQuasiStmtList' Map.empty

renameQuasiStmtList' :: NameEnv -> [QuasiStmt] -> WithEnv [QuasiStmt]
renameQuasiStmtList' _ [] = return []
renameQuasiStmtList' nenv ((QuasiStmtLet m (mx, x, t) e):ss) = do
  t' <- rename' nenv t
  x' <- newLLVMNameWith x
  e' <- rename' nenv e
  ss' <- renameQuasiStmtList' (insertName x x' nenv) ss
  return $ QuasiStmtLet m (mx, x', t') e' : ss'
renameQuasiStmtList' nenv ((QuasiStmtLetWT m (mx, x, t) e):ss) = do
  t' <- rename' nenv t
  x' <- newLLVMNameWith x
  e' <- rename' nenv e
  ss' <- renameQuasiStmtList' (insertName x x' nenv) ss
  return $ QuasiStmtLetWT m (mx, x', t') e' : ss'
renameQuasiStmtList' nenv ((QuasiStmtDef xds):ss) = do
  let (xs, ds) = unzip xds
  -- rename for deflist
  let ys = map (\(_, (_, y, _), _, _) -> y) ds
  ys' <- mapM newLLVMNameWith ys
  let yis = map asText ys
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
  -- e' <- rename' (Map.insert i 0 nenv) e
  -- ss' <- renameQuasiStmtList' (insertName x x nenv) ss
  ss' <- renameQuasiStmtList' nenv ss
  return $ QuasiStmtConstDecl m (mx, x, t') : ss'
renameQuasiStmtList' nenv ((QuasiStmtLetInductive n m (mx, a, t) e):ss) = do
  t' <- rename' nenv t
  a' <- newLLVMNameWith a
  e' <- rename' nenv e
  ss' <- renameQuasiStmtList' (insertName a a' nenv) ss
  return $ QuasiStmtLetInductive n m (mx, a', t') e' : ss'
renameQuasiStmtList' nenv ((QuasiStmtLetCoinductive n m (mx, a, t) e):ss) = do
  t' <- rename' nenv t
  a' <- newLLVMNameWith a
  e' <- rename' nenv e
  ss' <- renameQuasiStmtList' (insertName a a' nenv) ss
  return $ QuasiStmtLetCoinductive n m (mx, a', t') e' : ss'
renameQuasiStmtList' nenv ((QuasiStmtLetInductiveIntro m (mb, b, t) xts yts ats bts bInner _ _):ss) = do
  t' <- rename' nenv t
  (xts', nenv') <- renameArgs nenv xts
  (yts', nenv'') <- renameArgs nenv' yts
  (ats', nenv''') <- renameArgs nenv'' ats
  (bts', nenv'''') <- renameArgs nenv''' bts
  bInner' <- rename' nenv'''' bInner
  b' <- newLLVMNameWith b
  ss' <- renameQuasiStmtList' (insertName b b' nenv) ss
  asOuter <- mapM (lookupStrict nenv) ats
  asInnerPlus <- mapM (lookupStrict' nenv'''') ats
  let info = zip asOuter asInnerPlus
  return $
    QuasiStmtLetInductiveIntro
      m
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
  b' <- newLLVMNameWith b
  ss' <- renameQuasiStmtList' (insertName b b' nenv) ss
  asOuterPlus <- mapM (lookupStrict' nenv) ats
  asOuter <- mapM (lookupStrict nenv) ats
  asInner <- mapM (lookupStrict nenv'''') ats
  let info = zip asInner asOuterPlus
  -- p "renamed coinductiveelim. xtsytatsbts (before:)"
  -- p' $ xtsyt ++ ats ++ bts
  -- p "after:"
  -- p' $ xtsyt' ++ ats' ++ bts'
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

renameDef :: NameEnv -> Def -> WithEnv Def
renameDef nenv (m, (mx, x, t), xts, e) = do
  t' <- rename' nenv t
  (xts', e') <- renameBinder nenv xts e
  case lookupName x nenv of
    Nothing -> throwError' "renameDef"
    Just x' -> return (m, (mx, x', t'), xts', e')

-- type NameEnv = Map.HashMap Int Identifier
type NameEnv = Map.HashMap T.Text Int

-- Alpha-convert all the variables so that different variables have different names.
rename' :: NameEnv -> WeakTermPlus -> WithEnv WeakTermPlus
rename' _ (m, WeakTermTau l) = return (m, WeakTermTau l)
rename' nenv (m, WeakTermUpsilon x@(I (s, _))) = do
  mc <- lookupConstantMaybe s
  case (lookupName x nenv, mc) of
    (Just x', _) -> return (m, WeakTermUpsilon x')
    (_, Just c) -> return c
    _ -> throwError' $ T.pack (showMeta m) <> ": undefined variable: " <> s
rename' nenv (m, WeakTermPi mls xts t) = do
  (xts', t') <- renameBinder nenv xts t
  return (m, WeakTermPi mls xts' t')
rename' nenv (m, WeakTermPiIntro xts e) = do
  (xts', e') <- renameBinder nenv xts e
  return (m, WeakTermPiIntro xts' e')
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
rename' nenv (m, WeakTermConstDecl (mx, x, t) e) = do
  t' <- rename' nenv t
  e' <- rename' nenv e
  return (m, WeakTermConstDecl (mx, x, t') e')
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
lookupStrict nenv (_, x, _) =
  case lookupName x nenv of
    Just x' -> return x'
    Nothing -> throwError' $ "[lookupStrict] undefined variable:  " <> asText x

lookupStrict' :: NameEnv -> IdentifierPlus -> WithEnv WeakTermPlus
lookupStrict' nenv (m, x, _) =
  case lookupName x nenv of
    Just x' -> return (m, WeakTermUpsilon x')
    Nothing -> throwError' $ "[lookupStrict] undefined variable:  " <> asText x

checkSanity :: [Identifier] -> WeakTermPlus -> Bool
checkSanity _ (_, WeakTermTau _) = True
checkSanity _ (_, WeakTermUpsilon _) = True
checkSanity ctx (_, WeakTermPi _ xts t) = do
  checkSanity' ctx xts t
checkSanity ctx (_, WeakTermPiIntro xts e) = do
  checkSanity' ctx xts e
checkSanity ctx (_, WeakTermPiElim e es) = do
  checkSanity ctx e && all (checkSanity ctx) es
checkSanity ctx (_, WeakTermSigma xts) = checkSanitySigma ctx xts
checkSanity ctx (_, WeakTermSigmaIntro t es) = all (checkSanity ctx) $ t : es
checkSanity ctx (_, WeakTermSigmaElim t xts e1 e2) = do
  all (checkSanity ctx) [t, e1] && checkSanity' ctx xts e2
checkSanity ctx (_, WeakTermIter xt xts e) = do
  checkSanity' ctx (xt : xts) e
checkSanity _ (_, WeakTermConst _) = True
checkSanity ctx (_, WeakTermConstDecl (_, _, t) e) = do
  checkSanity ctx t && checkSanity ctx e
checkSanity _ (_, WeakTermZeta _) = True
checkSanity ctx (_, WeakTermInt t _) = checkSanity ctx t
checkSanity _ (_, WeakTermFloat16 _) = True
checkSanity _ (_, WeakTermFloat32 _) = True
checkSanity _ (_, WeakTermFloat64 _) = True
checkSanity ctx (_, WeakTermFloat t _) = checkSanity ctx t
checkSanity _ (_, WeakTermEnum _) = True
checkSanity _ (_, WeakTermEnumIntro _) = True
checkSanity ctx (_, WeakTermEnumElim (e, t) les) =
  all (checkSanity ctx) $ e : t : map snd les
checkSanity ctx (_, WeakTermArray dom _) = do
  checkSanity ctx dom
checkSanity ctx (_, WeakTermArrayIntro _ es) = do
  all (checkSanity ctx) es
checkSanity ctx (_, WeakTermArrayElim _ xts e1 e2) = do
  checkSanity ctx e1 && checkSanity' ctx xts e2
checkSanity _ (_, WeakTermStruct {}) = True
checkSanity ctx (_, WeakTermStructIntro ets) =
  all (checkSanity ctx) $ map fst ets
checkSanity ctx (_, WeakTermStructElim xts e1 e2) = do
  checkSanity ctx e1 && checkSanity'' ctx xts e2

checkSanity' :: [Identifier] -> [IdentifierPlus] -> WeakTermPlus -> Bool
checkSanity' ctx [] e = do
  checkSanity ctx e
checkSanity' ctx ((_, x, _):_) _
  | x `elem` ctx = False
checkSanity' ctx ((_, x, t):xts) e = do
  checkSanity ctx t && checkSanity' (x : ctx) xts e

checkSanitySigma :: [Identifier] -> [IdentifierPlus] -> Bool
checkSanitySigma _ [] = True
checkSanitySigma ctx ((_, x, _):_)
  | x `elem` ctx = False
checkSanitySigma ctx ((_, x, t):xts) = do
  checkSanity ctx t && checkSanitySigma (x : ctx) xts

checkSanity'' ::
     [Identifier] -> [(Meta, Identifier, ArrayKind)] -> WeakTermPlus -> Bool
checkSanity'' ctx [] e = do
  checkSanity ctx e
checkSanity'' ctx ((_, x, _):_) _
  | x `elem` ctx = False
checkSanity'' ctx ((_, x, _):xts) e = do
  checkSanity'' (x : ctx) xts e

prepareInvRename :: WithEnv ()
prepareInvRename = do
  modify (\env -> env {count = 0})

data IdentKind
  = IdentKindUpsilon
  | IdentKindZeta

-- fixme
invRenameIdentifier :: IdentKind -> Identifier -> WithEnv Identifier
invRenameIdentifier IdentKindUpsilon (I (s, i)) = do
  rnenv <- gets revNameEnv
  case Map.lookup i rnenv of
    Just i' -> do
      i'' <- traceIdentifier rnenv i'
      return $ I (s, i'')
    Nothing -> do
      j <- newCount
      let s' = T.pack $ "var" ++ show j
      -- fixme
      -- modify (\env -> env {revNameEnv = Map.insert i x s rnenv})
      return $ asIdent s'
invRenameIdentifier IdentKindZeta (I (s, i)) = do
  rnenv <- gets revNameEnv
  case Map.lookup i rnenv of
    Just i' -> do
      i'' <- traceIdentifier rnenv i'
      return $ I (s, i'')
    Nothing -> do
      j <- newCount
      let s' = T.pack $ "?M" ++ show j
      -- fixme
      -- modify (\env -> env {revNameEnv = insertName x s rnenv})
      return $ asIdent s'

traceIdentifier :: Map.HashMap Int Int -> Int -> WithEnv Int
traceIdentifier rnenv i = do
  case Map.lookup i rnenv of
    Nothing -> return i
    Just i' -> traceIdentifier rnenv i'

-- Alpha-convert all the variables so that different variables have different names.
invRename :: WeakTermPlus -> WithEnv WeakTermPlus
invRename (m, WeakTermTau l) = return (m, WeakTermTau l)
invRename (m, WeakTermUpsilon x) = do
  x' <- invRenameIdentifier IdentKindUpsilon x
  return (m, WeakTermUpsilon x')
invRename (m, WeakTermPi mls xts t) = do
  (xts', t') <- invRenameBinder xts t
  return (m, WeakTermPi mls xts' t')
invRename (m, WeakTermPiIntro xts e) = do
  (xts', e') <- invRenameBinder xts e
  return (m, WeakTermPiIntro xts' e')
invRename (m, WeakTermPiElim e es) = do
  e' <- invRename e
  es' <- mapM invRename es
  return (m, WeakTermPiElim e' es')
invRename (m, WeakTermSigma xts) =
  case splitLast xts of
    Nothing -> return (m, WeakTermSigma xts)
    Just (yts, (my, y, t)) -> do
      yts' <- invRenameSigma yts
      t' <- invRename t
      return (m, WeakTermSigma $ yts' ++ [(my, y, t')])
invRename (m, WeakTermSigmaIntro t es) = do
  es' <- mapM invRename es
  -- don't rename t since it is not printed
  return (m, WeakTermSigmaIntro t es')
invRename (m, WeakTermSigmaElim t xts e1 e2) = do
  e1' <- invRename e1
  (xts', e2') <- invRenameBinder xts e2
  return (m, WeakTermSigmaElim t xts' e1' e2')
invRename (m, WeakTermIter (mx, x, t) xts e) = do
  x' <- invRenameIdentifier IdentKindUpsilon x
  (xts', e') <- invRenameBinder xts e
  return (m, WeakTermIter (mx, x', t) xts' e')
invRename (m, WeakTermConst x) = return (m, WeakTermConst x)
invRename (m, WeakTermConstDecl (mx, x, t) e) = do
  t' <- invRename t
  e' <- invRename e
  return (m, WeakTermConstDecl (mx, x, t') e')
invRename (m, WeakTermZeta h) = do
  h' <- invRenameIdentifier IdentKindZeta h
  return (m, WeakTermZeta h')
invRename (m, WeakTermInt t x) = do
  return (m, WeakTermInt t x)
invRename (m, WeakTermFloat16 x) = return (m, WeakTermFloat16 x)
invRename (m, WeakTermFloat32 x) = return (m, WeakTermFloat32 x)
invRename (m, WeakTermFloat64 x) = return (m, WeakTermFloat64 x)
invRename (m, WeakTermFloat t x) = do
  return (m, WeakTermFloat t x)
invRename (m, WeakTermEnum s) = return (m, WeakTermEnum s)
invRename (m, WeakTermEnumIntro x) = return (m, WeakTermEnumIntro x)
invRename (m, WeakTermEnumElim (e, t) caseList) = do
  e' <- invRename e
  caseList' <- invRenameCaseList caseList
  return (m, WeakTermEnumElim (e', t) caseList')
invRename (m, WeakTermArray dom kind) = do
  dom' <- invRename dom
  return (m, WeakTermArray dom' kind)
invRename (m, WeakTermArrayIntro kind es) = do
  es' <- mapM invRename es
  return (m, WeakTermArrayIntro kind es')
invRename (m, WeakTermArrayElim kind xts e1 e2) = do
  e1' <- invRename e1
  (xts', e2') <- invRenameBinder xts e2
  return (m, WeakTermArrayElim kind xts' e1' e2')
invRename (m, WeakTermStruct ts) = return (m, WeakTermStruct ts)
invRename (m, WeakTermStructIntro ets) = do
  let (es, ts) = unzip ets
  es' <- mapM invRename es
  return (m, WeakTermStructIntro $ zip es' ts)
invRename (m, WeakTermStructElim xts e1 e2) = do
  e1' <- invRename e1
  (xts', e2') <- invRenameStruct xts e2
  return (m, WeakTermStructElim xts' e1' e2')

invRenameBinder ::
     [IdentifierPlus]
  -> WeakTermPlus
  -> WithEnv ([IdentifierPlus], WeakTermPlus)
invRenameBinder [] e = do
  e' <- invRename e
  return ([], e')
invRenameBinder ((mx, x, t):xts) e = do
  t' <- invRename t
  x' <- invRenameIdentifier IdentKindUpsilon x
  (xts', e') <- invRenameBinder xts e
  return ((mx, x', t') : xts', e')

invRenameSigma :: [IdentifierPlus] -> WithEnv [IdentifierPlus]
invRenameSigma [] = return []
invRenameSigma ((mx, x, t):xts) = do
  t' <- invRename t
  x' <- invRenameIdentifier IdentKindUpsilon x
  xts' <- invRenameSigma xts
  return $ (mx, x', t') : xts'

invRenameCaseList ::
     [(WeakCase, WeakTermPlus)] -> WithEnv [(WeakCase, WeakTermPlus)]
invRenameCaseList caseList = do
  let (ls, es) = unzip caseList
  ls' <- mapM invRenameWeakCase ls
  es' <- mapM invRename es
  return $ zip ls' es'

invRenameWeakCase :: WeakCase -> WithEnv WeakCase
invRenameWeakCase (WeakCaseInt t a) = do
  t' <- invRename t
  return $ WeakCaseInt t' a
invRenameWeakCase l = return l

invRenameStruct ::
     [(Meta, Identifier, ArrayKind)]
  -> WeakTermPlus
  -> WithEnv ([(Meta, Identifier, ArrayKind)], WeakTermPlus)
invRenameStruct [] e = do
  e' <- invRename e
  return ([], e')
invRenameStruct ((mx, x, t):xts) e = do
  x' <- invRenameIdentifier IdentKindUpsilon x
  (xts', e') <- invRenameStruct xts e
  return ((mx, x', t) : xts', e')

insertName :: Identifier -> Identifier -> NameEnv -> NameEnv
insertName (I (s, _)) (I (_, j)) nenv = Map.insert s j nenv

lookupName :: Identifier -> NameEnv -> Maybe Identifier
lookupName (I (s, _)) nenv = do
  j <- Map.lookup s nenv
  return $ I (llvmString s, j)
  -- return $ I (s, j)
