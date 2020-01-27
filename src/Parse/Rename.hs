{-# LANGUAGE OverloadedStrings #-}

module Parse.Rename
  ( rename
  , renameStmtList
  , invRename
  , prepareInvRename
  ) where

import Control.Monad.Except
import Control.Monad.State

-- import Data.Tuple (swap)
import qualified Data.HashMap.Strict as Map
import qualified Data.Text as T

import Data.Basic
import Data.Env
import Data.WeakTerm

-- {} rename' nenv {(every bound variable has fresh name)}
rename :: WeakTermPlus -> WithEnv WeakTermPlus
rename e = do
  result <- rename' Map.empty e
  let info = toInfo "rename.post" result
  return $ assertP info result $ checkSanity [] result

renameStmtList :: [Stmt] -> WithEnv [Stmt]
renameStmtList = renameStmtList' Map.empty

renameStmtList' :: NameEnv -> [Stmt] -> WithEnv [Stmt]
renameStmtList' _ [] = return []
renameStmtList' nenv ((StmtLet m (x, t) e):ss) = do
  t' <- rename' nenv t
  x' <- newLLVMNameWith x
  e' <- rename' nenv e
  ss' <- renameStmtList' (Map.insert x x' nenv) ss
  return $ StmtLet m (x', t') e' : ss'
renameStmtList' nenv ((StmtDef xds):ss) = do
  let (xs, ds) = unzip xds
  -- rename for deflist
  let ys = map (\(_, (y, _), _, _) -> y) ds
  ys' <- mapM newLLVMNameWith ys
  let nenvForDef = Map.fromList (zip ys ys') `Map.union` nenv
  ds' <- mapM (renameDef nenvForDef) ds
  -- rename for continuation
  xs' <- mapM newLLVMNameWith xs
  let nenvForCont = Map.fromList (zip xs xs') `Map.union` nenv
  ss' <- renameStmtList' nenvForCont ss
  return $ StmtDef (zip xs' ds') : ss'
renameStmtList' nenv ((StmtConstDecl (x, t)):ss) = do
  t' <- rename' nenv t
  ss' <- renameStmtList' (Map.insert x x nenv) ss
  return $ StmtConstDecl (x, t') : ss'

renameDef :: NameEnv -> Def -> WithEnv Def
renameDef nenv (m, (x, t), xts, e) = do
  t' <- rename' nenv t
  (xts', e') <- renameBinder nenv xts e
  case Map.lookup x nenv of
    Nothing -> throwError' "renameDef"
    Just x' -> return (m, (x', t'), xts', e')
  -- (xt', xts', e') <- renameIter nenv xt xts e
  -- (xts', e') <- renameBinder nenv xts e
  -- return (m, xt', xts', e')

type NameEnv = Map.HashMap Identifier Identifier

-- Alpha-convert all the variables so that different variables have different names.
rename' :: NameEnv -> WeakTermPlus -> WithEnv WeakTermPlus
rename' _ (m, WeakTermTau) = return (m, WeakTermTau)
rename' nenv (m, WeakTermUpsilon x) = do
  case Map.lookup x nenv of
    Just x'
      | x == x' -> return (m, WeakTermConst x')
    Just x' -> return (m, WeakTermUpsilon x')
    Nothing
      | isConstant x -> return (m, WeakTermConst x)
    Nothing ->
      throwError' $ T.pack (showMeta m) <> ": undefined variable: " <> x
rename' nenv (m, WeakTermPi xts t) = do
  (xts', t') <- renameBinder nenv xts t
  return (m, WeakTermPi xts' t')
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
rename' nenv (m, WeakTermConstDecl (x, t) e) = do
  t' <- rename' nenv t
  e' <- rename' (Map.insert x x nenv) e
  return (m, WeakTermConstDecl (x, t') e')
rename' _ (m, WeakTermZeta h) = return (m, WeakTermZeta h)
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
renameBinder nenv ((x, t):xts) e = do
  t' <- rename' nenv t
  x' <- newLLVMNameWith x
  (xts', e') <- renameBinder (Map.insert x x' nenv) xts e
  return ((x', t') : xts', e')

renameSigma :: NameEnv -> [IdentifierPlus] -> WithEnv [IdentifierPlus]
renameSigma _ [] = return []
renameSigma nenv ((x, t):xts) = do
  t' <- rename' nenv t
  x' <- newLLVMNameWith x
  xts' <- renameSigma (Map.insert x x' nenv) xts
  return $ (x', t') : xts'

renameIter ::
     NameEnv
  -> IdentifierPlus
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> WithEnv (IdentifierPlus, [IdentifierPlus], WeakTermPlus)
renameIter nenv (x, t) xts e = do
  t' <- rename' nenv t
  renameIter' nenv (x, t') xts e

renameIter' ::
     NameEnv
  -> IdentifierPlus
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> WithEnv (IdentifierPlus, [IdentifierPlus], WeakTermPlus)
renameIter' nenv (x, t') [] e = do
  x' <- newLLVMNameWith x
  e' <- rename' (Map.insert x x' nenv) e
  return ((x', t'), [], e')
renameIter' nenv xt ((x, t):xts) e = do
  t' <- rename' nenv t
  x' <- newLLVMNameWith x
  (xt', xts', e') <- renameIter' (Map.insert x x' nenv) xt xts e
  return (xt', (x', t') : xts', e')

renameCaseList ::
     NameEnv -> [(Case, WeakTermPlus)] -> WithEnv [(Case, WeakTermPlus)]
renameCaseList nenv caseList =
  forM caseList $ \(l, body) -> do
    body' <- rename' nenv body
    return (l, body')

renameStruct ::
     NameEnv
  -> [(Identifier, ArrayKind)]
  -> WeakTermPlus
  -> WithEnv ([(Identifier, ArrayKind)], WeakTermPlus)
renameStruct nenv [] e = do
  e' <- rename' nenv e
  return ([], e')
renameStruct nenv ((x, t):xts) e = do
  x' <- newLLVMNameWith x
  (xts', e') <- renameStruct (Map.insert x x' nenv) xts e
  return ((x', t) : xts', e')

checkSanity :: [Identifier] -> WeakTermPlus -> Bool
checkSanity _ (_, WeakTermTau) = True
checkSanity _ (_, WeakTermUpsilon _) = True
checkSanity ctx (_, WeakTermPi xts t) = do
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
checkSanity ctx (_, WeakTermConstDecl (_, t) e) = do
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
checkSanity' ctx ((x, _):_) _
  | x `elem` ctx = False
checkSanity' ctx ((x, t):xts) e = do
  checkSanity ctx t && checkSanity' (x : ctx) xts e

checkSanitySigma :: [Identifier] -> [IdentifierPlus] -> Bool
checkSanitySigma _ [] = True
checkSanitySigma ctx ((x, _):_)
  | x `elem` ctx = False
checkSanitySigma ctx ((x, t):xts) = do
  checkSanity ctx t && checkSanitySigma (x : ctx) xts

checkSanity'' ::
     [Identifier] -> [(Identifier, ArrayKind)] -> WeakTermPlus -> Bool
checkSanity'' ctx [] e = do
  checkSanity ctx e
checkSanity'' ctx ((x, _):_) _
  | x `elem` ctx = False
checkSanity'' ctx ((x, _):xts) e = do
  checkSanity'' (x : ctx) xts e

-- {} invRename {(every bound variable has fresh name)}
prepareInvRename :: WithEnv ()
prepareInvRename = do
  modify (\env -> env {count = 0})

data IdentKind
  = IdentKindUpsilon
  | IdentKindZeta

invRenameIdentifier :: IdentKind -> Identifier -> WithEnv Identifier
invRenameIdentifier IdentKindUpsilon x = do
  rnenv <- gets revNameEnv
  case Map.lookup x rnenv of
    Just x' -> traceIdentifier rnenv x'
    Nothing -> do
      i <- newCount
      let s = T.pack $ "var" ++ show i
      modify (\env -> env {revNameEnv = Map.insert x s rnenv})
      return s
invRenameIdentifier IdentKindZeta x = do
  rnenv <- gets revNameEnv
  case Map.lookup x rnenv of
    Just x' -> traceIdentifier rnenv x'
    Nothing -> do
      i <- newCount
      let s = T.pack $ "?M" ++ show i
      modify (\env -> env {revNameEnv = Map.insert x s rnenv})
      return s

traceIdentifier :: NameEnv -> Identifier -> WithEnv Identifier
traceIdentifier rnenv x = do
  case Map.lookup x rnenv of
    Nothing -> return x
    Just x' -> traceIdentifier rnenv x'

-- Alpha-convert all the variables so that different variables have different names.
invRename :: WeakTermPlus -> WithEnv WeakTermPlus
invRename (m, WeakTermTau) = return (m, WeakTermTau)
invRename (m, WeakTermUpsilon x) = do
  x' <- invRenameIdentifier IdentKindUpsilon x
  return (m, WeakTermUpsilon x')
invRename (m, WeakTermPi xts t) = do
  (xts', t') <- invRenameBinder xts t
  return (m, WeakTermPi xts' t')
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
    Just (yts, (y, t)) -> do
      yts' <- invRenameSigma yts
      t' <- invRename t
      return (m, WeakTermSigma $ yts' ++ [(y, t')])
invRename (m, WeakTermSigmaIntro t es) = do
  es' <- mapM invRename es
  -- don't rename t since it is not printed
  return (m, WeakTermSigmaIntro t es')
invRename (m, WeakTermSigmaElim t xts e1 e2) = do
  e1' <- invRename e1
  (xts', e2') <- invRenameBinder xts e2
  return (m, WeakTermSigmaElim t xts' e1' e2')
invRename (m, WeakTermIter (x, t) xts e) = do
  x' <- invRenameIdentifier IdentKindUpsilon x
  (xts', e') <- invRenameBinder xts e
  return (m, WeakTermIter (x', t) xts' e')
invRename (m, WeakTermConst x) = return (m, WeakTermConst x)
invRename (m, WeakTermConstDecl (x, t) e) = do
  t' <- invRename t
  e' <- invRename e
  return (m, WeakTermConstDecl (x, t') e')
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
invRenameBinder ((x, t):xts) e = do
  t' <- invRename t
  x' <- invRenameIdentifier IdentKindUpsilon x
  (xts', e') <- invRenameBinder xts e
  return ((x', t') : xts', e')

invRenameSigma :: [IdentifierPlus] -> WithEnv [IdentifierPlus]
invRenameSigma [] = return []
invRenameSigma ((x, t):xts) = do
  t' <- invRename t
  x' <- invRenameIdentifier IdentKindUpsilon x
  xts' <- invRenameSigma xts
  return $ (x', t') : xts'

invRenameCaseList :: [(Case, WeakTermPlus)] -> WithEnv [(Case, WeakTermPlus)]
invRenameCaseList caseList = do
  let (ls, es) = unzip caseList
  es' <- mapM invRename es
  return $ zip ls es'

invRenameStruct ::
     [(Identifier, ArrayKind)]
  -> WeakTermPlus
  -> WithEnv ([(Identifier, ArrayKind)], WeakTermPlus)
invRenameStruct [] e = do
  e' <- invRename e
  return ([], e')
invRenameStruct ((x, t):xts) e = do
  x' <- invRenameIdentifier IdentKindUpsilon x
  (xts', e') <- invRenameStruct xts e
  return ((x', t) : xts', e')
