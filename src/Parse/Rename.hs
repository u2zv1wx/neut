{-# LANGUAGE OverloadedStrings #-}

module Parse.Rename
  ( rename
  ) where

import Control.Monad.Except
import Control.Monad.State

import qualified Data.HashMap.Strict as Map
import qualified Data.Text as T

import Data.Basic
import Data.Env
import Data.WeakTerm

-- {} rename' {(every bound variable has fresh name)}
rename :: WeakTermPlus -> WithEnv WeakTermPlus
rename e = do
  result <- rename' e
  let info = toInfo "rename.post" result
  return $ assertP info result $ checkSanity [] result

-- Alpha-convert all the variables so that different variables have different names.
rename' :: WeakTermPlus -> WithEnv WeakTermPlus
rename' (m, WeakTermTau) = return (m, WeakTermTau)
rename' (m, WeakTermUpsilon x) = do
  nenv <- gets nameEnv
  case Map.lookup x nenv of
    Just x'
      | x == x' -> return (m, WeakTermConst x')
    Just x' -> return (m, WeakTermUpsilon x')
    Nothing
      | isConstant x -> return (m, WeakTermConst x)
    Nothing -> throwError $ T.pack (showMeta m) <> ": undefined variable: " <> x
rename' (m, WeakTermPi xts t) = do
  (xts', t') <- renameBinder xts t
  return (m, WeakTermPi xts' t')
rename' (m, WeakTermPiIntro xts e) = do
  (xts', e') <- renameBinder xts e
  return (m, WeakTermPiIntro xts' e')
rename' (m, WeakTermPiElim e es) = do
  e' <- rename' e
  es' <- mapM rename' es
  return (m, WeakTermPiElim e' es')
rename' (m, WeakTermSigma xts) = do
  xts' <- renameSigma xts
  return (m, WeakTermSigma xts')
rename' (m, WeakTermSigmaIntro t es) = do
  t' <- rename' t
  es' <- mapM rename' es
  return (m, WeakTermSigmaIntro t' es')
rename' (m, WeakTermSigmaElim t xts e1 e2) = do
  t' <- rename' t
  e1' <- rename' e1
  (xts', e2') <- renameBinder xts e2
  return (m, WeakTermSigmaElim t' xts' e1' e2')
rename' (m, WeakTermIter xt xts e) = do
  (xt', xts', e') <- renameIter xt xts e
  return (m, WeakTermIter xt' xts' e')
rename' (m, WeakTermConst x) = return (m, WeakTermConst x)
rename' (m, WeakTermConstDecl (x, t) e) = do
  t' <- rename' t
  modify (\env -> env {nameEnv = Map.insert x x (nameEnv env)})
  e' <- rename' e
  return (m, WeakTermConstDecl (x, t') e')
rename' (m, WeakTermZeta h) = return (m, WeakTermZeta h)
rename' (m, WeakTermInt t x) = do
  t' <- rename t
  return (m, WeakTermInt t' x)
rename' (m, WeakTermFloat16 x) = return (m, WeakTermFloat16 x)
rename' (m, WeakTermFloat32 x) = return (m, WeakTermFloat32 x)
rename' (m, WeakTermFloat64 x) = return (m, WeakTermFloat64 x)
rename' (m, WeakTermFloat t x) = do
  t' <- rename' t
  return (m, WeakTermFloat t' x)
rename' (m, WeakTermEnum s) = return (m, WeakTermEnum s)
rename' (m, WeakTermEnumIntro x) = return (m, WeakTermEnumIntro x)
rename' (m, WeakTermEnumElim (e, t) caseList) = do
  e' <- rename' e
  t' <- rename' t
  caseList' <- renameCaseList caseList
  return (m, WeakTermEnumElim (e', t') caseList')
rename' (m, WeakTermArray dom kind) = do
  dom' <- rename' dom
  return (m, WeakTermArray dom' kind)
rename' (m, WeakTermArrayIntro kind es) = do
  es' <- mapM rename' es
  return (m, WeakTermArrayIntro kind es')
rename' (m, WeakTermArrayElim kind xts e1 e2) = do
  e1' <- rename' e1
  (xts', e2') <- renameBinder xts e2
  return (m, WeakTermArrayElim kind xts' e1' e2')
rename' (m, WeakTermStruct ts) = return (m, WeakTermStruct ts)
rename' (m, WeakTermStructIntro ets) = do
  let (es, ts) = unzip ets
  es' <- mapM rename' es
  return (m, WeakTermStructIntro $ zip es' ts)
rename' (m, WeakTermStructElim xts e1 e2) = do
  e1' <- rename' e1
  (xts', e2') <- renameStruct xts e2
  return (m, WeakTermStructElim xts' e1' e2')

renameBinder ::
     [IdentifierPlus]
  -> WeakTermPlus
  -> WithEnv ([IdentifierPlus], WeakTermPlus)
renameBinder [] e = do
  e' <- rename' e
  return ([], e')
renameBinder ((x, t):xts) e = do
  t' <- rename' t
  local $ do
    x' <- newLLVMNameWith x
    (xts', e') <- renameBinder xts e
    return ((x', t') : xts', e')

renameSigma :: [IdentifierPlus] -> WithEnv [IdentifierPlus]
renameSigma [] = return []
renameSigma ((x, t):xts) = do
  t' <- rename' t
  local $ do
    x' <- newLLVMNameWith x
    xts' <- renameSigma xts
    return $ (x', t') : xts'

renameIter ::
     IdentifierPlus
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> WithEnv (IdentifierPlus, [IdentifierPlus], WeakTermPlus)
renameIter (x, t) xts e = do
  t' <- rename' t
  renameIter' (x, t') xts e

renameIter' ::
     IdentifierPlus
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> WithEnv (IdentifierPlus, [IdentifierPlus], WeakTermPlus)
renameIter' (x, t') [] e = do
  local $ do
    x' <- newLLVMNameWith x
    e' <- rename' e
    return ((x', t'), [], e')
renameIter' xt ((x, t):xts) e = do
  t' <- rename' t
  local $ do
    x' <- newLLVMNameWith x
    (xt', xts', e') <- renameIter' xt xts e
    return (xt', (x', t') : xts', e')

renameCaseList :: [(Case, WeakTermPlus)] -> WithEnv [(Case, WeakTermPlus)]
renameCaseList caseList =
  forM caseList $ \(l, body) ->
    local $ do
      body' <- rename' body
      return (l, body')

renameStruct ::
     [(Identifier, ArrayKind)]
  -> WeakTermPlus
  -> WithEnv ([(Identifier, ArrayKind)], WeakTermPlus)
renameStruct [] e = do
  e' <- rename' e
  return ([], e')
renameStruct ((x, t):xts) e = do
  local $ do
    x' <- newLLVMNameWith x
    (xts', e') <- renameStruct xts e
    return ((x', t) : xts', e')

local :: WithEnv a -> WithEnv a
local comp = do
  env <- get
  x <- comp
  modify (\e -> env {count = count e})
  return x

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
