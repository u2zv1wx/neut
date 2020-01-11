module Parse.Rename
  ( rename
  ) where

import Control.Monad.State

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
  x' <- lookupNameEnv x
  return (m, WeakTermUpsilon x')
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
rename' (m, WeakTermIter xt xts e) = do
  (xt', xts', e') <- renameIter xt xts e
  return (m, WeakTermIter xt' xts' e')
rename' (m, WeakTermConst x) = return (m, WeakTermConst x)
rename' (m, WeakTermConstDecl (x, t) e) = do
  t' <- rename' t
  e' <- rename' e
  return (m, WeakTermConstDecl (x, t') e')
rename' (m, WeakTermZeta h) = return (m, WeakTermZeta h)
rename' (m, WeakTermIntS size x) = return (m, WeakTermIntS size x)
rename' (m, WeakTermIntU size x) = return (m, WeakTermIntU size x)
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
rename' (m, WeakTermArray kind indexType) = do
  indexType' <- rename' indexType
  return (m, WeakTermArray kind indexType')
rename' (m, WeakTermArrayIntro kind les) = do
  les' <-
    forM les $ \(l, body) -> do
      body' <- rename' body
      return (l, body')
  return (m, WeakTermArrayIntro kind les')
rename' (m, WeakTermArrayElim kind e1 e2) = do
  e1' <- rename' e1
  e2' <- rename' e2
  return (m, WeakTermArrayElim kind e1' e2')

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
    x' <- newNameWith x
    (xts', e') <- renameBinder xts e
    return ((x', t') : xts', e')

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
    x' <- newNameWith x
    e' <- rename' e
    return ((x', t'), [], e')
renameIter' xt ((x, t):xts) e = do
  t' <- rename' t
  local $ do
    x' <- newNameWith x
    (xt', xts', e') <- renameIter' xt xts e
    return (xt', (x', t') : xts', e')

renameCaseList :: [(Case, WeakTermPlus)] -> WithEnv [(Case, WeakTermPlus)]
renameCaseList caseList =
  forM caseList $ \(l, body) ->
    local $ do
      body' <- rename' body
      return (l, body')

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
checkSanity ctx (_, WeakTermIter xt xts e) = do
  checkSanity' ctx (xt : xts) e
checkSanity _ (_, WeakTermConst _) = True
checkSanity ctx (_, WeakTermConstDecl (_, t) e) = do
  checkSanity ctx t && checkSanity ctx e
checkSanity _ (_, WeakTermZeta _) = True
checkSanity _ (_, WeakTermIntS {}) = True
checkSanity _ (_, WeakTermIntU {}) = True
checkSanity ctx (_, WeakTermInt t _) = checkSanity ctx t
checkSanity _ (_, WeakTermFloat16 _) = True
checkSanity _ (_, WeakTermFloat32 _) = True
checkSanity _ (_, WeakTermFloat64 _) = True
checkSanity ctx (_, WeakTermFloat t _) = checkSanity ctx t
checkSanity _ (_, WeakTermEnum _) = True
checkSanity _ (_, WeakTermEnumIntro _) = True
checkSanity ctx (_, WeakTermEnumElim (e, t) les) =
  all (checkSanity ctx) $ e : t : map snd les
checkSanity ctx (_, WeakTermArray _ indexType) = do
  checkSanity ctx indexType
checkSanity ctx (_, WeakTermArrayIntro _ les) = do
  all (checkSanity ctx . snd) les
checkSanity ctx (_, WeakTermArrayElim _ e1 e2) = do
  checkSanity ctx e1 && checkSanity ctx e2

checkSanity' :: [Identifier] -> [IdentifierPlus] -> WeakTermPlus -> Bool
checkSanity' ctx [] e = do
  checkSanity ctx e
checkSanity' ctx ((x, _):_) _
  | x `elem` ctx = False
checkSanity' ctx ((x, t):xts) e = do
  checkSanity ctx t && checkSanity' (x : ctx) xts e
