module Parse.Rename
  ( rename
  ) where

import Control.Monad.State

import Data.Basic
import Data.Env
import Data.WeakTerm

-- Alpha-convert all the variables so that different variables have different names.
rename :: WeakTermPlus -> WithEnv WeakTermPlus
rename (m, WeakTermTau) = return (m, WeakTermTau)
rename (m, WeakTermUpsilon x)
  | isConstant x = return (m, WeakTermUpsilon x) -- enum.n8, i64, f16, etc. shouldn't be renamed (i.e. can occur freely)
  | otherwise = do
    x' <- lookupNameEnv x
    return (m, WeakTermUpsilon x')
rename (m, WeakTermPi xts t) = do
  (xts', t') <- renameBinderWithBody xts t
  return (m, WeakTermPi xts' t')
rename (m, WeakTermPiIntro xts e) = do
  (xts', e') <- renameBinderWithBody xts e
  return (m, WeakTermPiIntro xts' e')
rename (m, WeakTermPiElim e es) = do
  e' <- rename e
  es' <- mapM rename es
  return (m, WeakTermPiElim e' es')
rename (m, WeakTermMu (x, t) e) =
  local $ do
    t' <- rename t
    x' <- newNameWith x
    e' <- rename e
    return (m, WeakTermMu (x', t') e')
rename (m, WeakTermTheta (x, t) e) = do
  local $ do
    t' <- rename t
    modify (\env -> env {nameEnv = (x, x) : nameEnv env}) -- constants shouldn't be alpha-converted
    e' <- rename e
    return (m, WeakTermMu (x, t') e')
rename (m, WeakTermZeta h) = return (m, WeakTermZeta h)
rename (m, WeakTermIntS size x) = return (m, WeakTermIntS size x)
rename (m, WeakTermIntU size x) = return (m, WeakTermIntU size x)
rename (m, WeakTermInt x) = return (m, WeakTermInt x)
rename (m, WeakTermFloat16 x) = return (m, WeakTermFloat16 x)
rename (m, WeakTermFloat32 x) = return (m, WeakTermFloat32 x)
rename (m, WeakTermFloat64 x) = return (m, WeakTermFloat64 x)
rename (m, WeakTermFloat x) = return (m, WeakTermFloat x)
rename (m, WeakTermEnum s) = return (m, WeakTermEnum s)
rename (m, WeakTermEnumIntro x) = return (m, WeakTermEnumIntro x)
rename (m, WeakTermEnumElim e caseList) = do
  e' <- rename e
  caseList' <- renameCaseList caseList
  return (m, WeakTermEnumElim e' caseList')
rename (m, WeakTermArray kind indexType) = do
  indexType' <- rename indexType
  return (m, WeakTermArray kind indexType')
rename (m, WeakTermArrayIntro kind les) = do
  les' <-
    forM les $ \(l, body) -> do
      body' <- rename body
      return (l, body')
  return (m, WeakTermArrayIntro kind les')
rename (m, WeakTermArrayElim kind e1 e2) = do
  e1' <- rename e1
  e2' <- rename e2
  return (m, WeakTermArrayElim kind e1' e2')

renameBinderWithBody ::
     [IdentifierPlus]
  -> WeakTermPlus
  -> WithEnv ([IdentifierPlus], WeakTermPlus)
renameBinderWithBody [] e = do
  e' <- rename e
  return ([], e')
renameBinderWithBody ((x, t):xts) e = do
  t' <- rename t
  local $ do
    x' <- newNameWith x
    (xts', e') <- renameBinderWithBody xts e
    return ((x', t') : xts', e')

renameCaseList :: [(Case, WeakTermPlus)] -> WithEnv [(Case, WeakTermPlus)]
renameCaseList caseList =
  forM caseList $ \(l, body) ->
    local $ do
      body' <- rename body
      return (l, body')

local :: WithEnv a -> WithEnv a
local comp = do
  env <- get
  x <- comp
  modify (\e -> env {count = count e})
  return x
