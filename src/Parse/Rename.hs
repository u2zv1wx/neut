module Parse.Rename
  ( rename
  ) where

import           Control.Monad.State

import           Data.Basic
import           Data.Env
import           Data.WeakTerm

-- Alpha-convert all the variables so that different variables have different names.
rename :: WeakTermPlus -> WithEnv WeakTermPlus
rename (m, WeakTermTau) = return (m, WeakTermTau)
rename (m, WeakTermTheta x) = return (m, WeakTermTheta x)
rename (m, WeakTermUpsilon x) = do
  x' <- lookupNameEnv x
  return (m, WeakTermUpsilon x')
rename (m, WeakTermEpsilon s) = return (m, WeakTermEpsilon s)
rename (m, WeakTermEpsilonIntro x) = return (m, WeakTermEpsilonIntro x)
rename (m, WeakTermEpsilonElim (x, t) e caseList) = do
  e' <- rename e
  t' <- rename t
  local $ do
    x' <- newNameWith x
    caseList' <- renameCaseList caseList
    return (m, WeakTermEpsilonElim (x', t') e' caseList')
rename (m, WeakTermPi xts t) = do
  (xts', t') <- renameBinder xts t
  return (m, WeakTermPi xts' t')
rename (m, WeakTermPiIntro xts e) = do
  (xts', e') <- renameBinder xts e
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
rename (m, WeakTermZeta h) = return (m, WeakTermZeta h)

renameBinder ::
     [IdentifierPlus]
  -> WeakTermPlus
  -> WithEnv ([IdentifierPlus], WeakTermPlus)
renameBinder [] e = do
  e' <- rename e
  return ([], e')
renameBinder ((x, t):xts) e = do
  t' <- rename t
  local $ do
    x' <- newNameWith x
    (xts', e') <- renameBinder xts e
    return ((x', t') : xts', e')

renameCaseList :: [(Case, WeakTermPlus)] -> WithEnv [(Case, WeakTermPlus)]
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
