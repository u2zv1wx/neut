module Parse.Rename
  ( rename
  ) where

import           Control.Comonad.Cofree
import           Control.Monad.State

import           Data.Basic
import           Data.Env
import           Data.WeakTerm

-- Alpha-convert all the variables so that different variables have different names.
rename :: WeakTerm -> WithEnv WeakTerm
rename (m :< WeakTermTau) = return $ m :< WeakTermTau
rename (m :< WeakTermTheta x) = return $ m :< WeakTermTheta x
rename (m :< WeakTermUpsilon x) = do
  x' <- lookupNameEnv x
  return $ m :< WeakTermUpsilon x'
rename (m :< WeakTermEpsilon s) = return $ m :< WeakTermEpsilon s
rename (m :< WeakTermEpsilonIntro x) = return $ m :< WeakTermEpsilonIntro x
rename (m :< WeakTermEpsilonElim (x, t) e caseList) = do
  e' <- rename e
  t' <- rename t
  local $ do
    x' <- newNameWith x
    caseList' <- renameCaseList caseList
    return $ m :< WeakTermEpsilonElim (x', t') e' caseList'
rename (m :< WeakTermPi xts) = do
  xts' <- renameBindings xts
  return $ m :< WeakTermPi xts'
rename (m :< WeakTermPiIntro xts e) = do
  (xts', e') <- renameBindingsWithBody xts e
  return $ m :< WeakTermPiIntro xts' e'
rename (m :< WeakTermPiElim e es) = do
  e' <- rename e
  es' <- mapM rename es
  return $ m :< WeakTermPiElim e' es'
rename (m :< WeakTermSigma xts) = do
  xts' <- renameBindings xts
  return $ m :< WeakTermSigma xts'
rename (m :< WeakTermSigmaIntro es) = do
  es' <- mapM rename es
  return $ m :< WeakTermSigmaIntro es'
rename (m :< WeakTermSigmaElim xts e1 e2) = do
  e1' <- rename e1
  (xts', e2') <- renameBindingsWithBody xts e2
  return $ m :< WeakTermSigmaElim xts' e1' e2'
rename (m :< WeakTermMu (x, t) e) =
  local $ do
    t' <- rename t
    x' <- newNameWith x
    e' <- rename e
    return $ m :< WeakTermMu (x', t') e'
rename (m :< WeakTermZeta h) = return $ m :< WeakTermZeta h

renameBindings :: [IdentifierPlus] -> WithEnv [IdentifierPlus]
renameBindings [] = return []
renameBindings ((x, t):xts) = do
  t' <- rename t
  local $ do
    x' <- newNameWith x
    xts' <- renameBindings xts
    return $ (x', t') : xts'

renameBindingsWithBody ::
     [IdentifierPlus] -> WeakTerm -> WithEnv ([IdentifierPlus], WeakTerm)
renameBindingsWithBody [] e = do
  e' <- rename e
  return ([], e')
renameBindingsWithBody ((x, t):xts) e = do
  t' <- rename t
  local $ do
    x' <- newNameWith x
    (xts', e') <- renameBindingsWithBody xts e
    return ((x', t') : xts', e')

renameCaseList :: [(Case, WeakTerm)] -> WithEnv [(Case, WeakTerm)]
renameCaseList caseList =
  forM caseList $ \(l, body) ->
    local $ do
      body' <- rename body
      return (l, body')

local :: WithEnv a -> WithEnv a
local p = do
  env <- get
  x <- p
  modify (\e -> env {count = count e})
  return x
