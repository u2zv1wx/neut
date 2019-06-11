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
rename (i :< WeakTermVar s) = do
  t <- WeakTermVar <$> lookupNameEnv s
  return $ i :< t
rename (i :< WeakTermConst x) = return $ i :< WeakTermConst x
rename (i :< WeakTermPi (s, tdom) tcod) = do
  tdom' <- rename tdom
  local $ do
    s' <- newNameWith s
    tcod' <- rename tcod
    return $ i :< WeakTermPi (s', tdom') tcod'
rename (i :< WeakTermPiIntro (s, tdom) e) = do
  tdom' <- rename tdom
  local $ do
    s' <- newNameWith s
    e' <- rename e
    return $ i :< WeakTermPiIntro (s', tdom') e'
rename (i :< WeakTermPiElim e v) = do
  e' <- rename e
  v' <- rename v
  return $ i :< WeakTermPiElim e' v'
rename (i :< WeakTermSigma xts) = do
  xts' <- renameSigma xts
  return $ i :< WeakTermSigma xts'
rename (i :< WeakTermSigmaIntro es) = do
  es' <- mapM rename es
  return $ i :< WeakTermSigmaIntro es'
rename (i :< WeakTermSigmaElim xs e1 e2) = do
  e1' <- rename e1
  local $ do
    xs' <- mapM newNameWith xs
    e2' <- rename e2
    return $ i :< WeakTermSigmaElim xs' e1' e2'
rename (i :< WeakTermIndex s) = return $ i :< WeakTermIndex s
rename (i :< WeakTermIndexIntro x) = return $ i :< WeakTermIndexIntro x
rename (i :< WeakTermIndexElim e branchList) = do
  e' <- rename e
  branchList' <- renameBranchList branchList
  return $ i :< WeakTermIndexElim e' branchList'
rename (i :< WeakTermUniv j) = return $ i :< WeakTermUniv j
rename (i :< WeakTermFix s e) =
  local $ do
    s' <- newNameWith s
    e' <- rename e
    return $ i :< WeakTermFix s' e'
rename (i :< WeakTermHole x) = return $ i :< WeakTermHole x

renameSigma :: [(Identifier, WeakTerm)] -> WithEnv [(Identifier, WeakTerm)]
renameSigma [] = return []
renameSigma ((x, t):xts) = do
  t' <- rename t
  local $ do
    x' <- newNameWith x
    xts' <- renameSigma xts
    return $ (x', t') : xts'

renameBranchList :: [(Index, WeakTerm)] -> WithEnv [(Index, WeakTerm)]
renameBranchList branchList =
  forM branchList $ \(l, body) ->
    local $ do
      body' <- rename body
      return (l, body')

local :: WithEnv a -> WithEnv a
local p = do
  env <- get
  x <- p
  modify (\e -> env {count = count e})
  return x
