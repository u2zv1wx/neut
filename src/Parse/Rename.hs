module Parse.Rename
  ( rename
  ) where

import Control.Monad.State

import Data.Basic
import Data.Env
import Data.QuasiTerm

-- Alpha-convert all the variables so that different variables have different names.
rename :: QuasiTermPlus -> WithEnv QuasiTermPlus
rename (m, QuasiTermTau) = return (m, QuasiTermTau)
rename (m, QuasiTermUpsilon x) = do
  x' <- lookupNameEnv x
  return (m, QuasiTermUpsilon x')
rename (m, QuasiTermPi xts t) = do
  (xts', t') <- renameBinderWithBody xts t
  return (m, QuasiTermPi xts' t')
rename (m, QuasiTermPiIntro xts e) = do
  (xts', e') <- renameBinderWithBody xts e
  return (m, QuasiTermPiIntro xts' e')
rename (m, QuasiTermPiElim e es) = do
  e' <- rename e
  es' <- mapM rename es
  return (m, QuasiTermPiElim e' es')
rename (m, QuasiTermMu (x, t) e) = do
  t' <- rename t
  local $ do
    x' <- newNameWith x
    e' <- rename e
    return (m, QuasiTermMu (x', t') e')
rename (m, QuasiTermConst x) = return (m, QuasiTermConst x)
rename (m, QuasiTermConstDecl (x, t) e) = do
  t' <- rename t
  e' <- rename e
  return (m, QuasiTermConstDecl (x, t') e')
rename (m, QuasiTermZeta h) = return (m, QuasiTermZeta h)
rename (m, QuasiTermIntS size x) = return (m, QuasiTermIntS size x)
rename (m, QuasiTermIntU size x) = return (m, QuasiTermIntU size x)
rename (m, QuasiTermInt x) = return (m, QuasiTermInt x)
rename (m, QuasiTermFloat16 x) = return (m, QuasiTermFloat16 x)
rename (m, QuasiTermFloat32 x) = return (m, QuasiTermFloat32 x)
rename (m, QuasiTermFloat64 x) = return (m, QuasiTermFloat64 x)
rename (m, QuasiTermFloat x) = return (m, QuasiTermFloat x)
rename (m, QuasiTermEnum s) = return (m, QuasiTermEnum s)
rename (m, QuasiTermEnumIntro x) = return (m, QuasiTermEnumIntro x)
rename (m, QuasiTermEnumElim e caseList) = do
  e' <- rename e
  caseList' <- renameCaseList caseList
  return (m, QuasiTermEnumElim e' caseList')
rename (m, QuasiTermArray kind indexType) = do
  indexType' <- rename indexType
  return (m, QuasiTermArray kind indexType')
rename (m, QuasiTermArrayIntro kind les) = do
  les' <-
    forM les $ \(l, body) -> do
      body' <- rename body
      return (l, body')
  return (m, QuasiTermArrayIntro kind les')
rename (m, QuasiTermArrayElim kind e1 e2) = do
  e1' <- rename e1
  e2' <- rename e2
  return (m, QuasiTermArrayElim kind e1' e2')

renameBinderWithBody ::
     [IdentifierPlus]
  -> QuasiTermPlus
  -> WithEnv ([IdentifierPlus], QuasiTermPlus)
renameBinderWithBody [] e = do
  e' <- rename e
  return ([], e')
renameBinderWithBody ((x, t):xts) e = do
  t' <- rename t
  local $ do
    x' <- newNameWith x
    (xts', e') <- renameBinderWithBody xts e
    return ((x', t') : xts', e')

renameCaseList :: [(Case, QuasiTermPlus)] -> WithEnv [(Case, QuasiTermPlus)]
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
