module Rename
  ( rename
  ) where

import Control.Monad.State
import Control.Monad.Trans.Except

import Control.Comonad.Cofree

import Data

import qualified Text.Show.Pretty as Pr

-- Alpha-convert all the variables so that different variables have different names.
rename :: Neut -> WithEnv Neut
rename (i :< NeutVar s) = do
  t <- NeutVar <$> lookupNameEnv s
  return $ i :< t
rename (i :< NeutPi (s, tdom) tcod) = do
  tdom' <- rename tdom
  local $ do
    s' <- newNameWith s
    tcod' <- rename tcod
    return $ i :< NeutPi (s', tdom') tcod'
rename (i :< NeutPiIntro (s, tdom) e) = do
  tdom' <- rename tdom
  local $ do
    s' <- newNameWith s
    e' <- rename e
    return $ i :< NeutPiIntro (s', tdom') e'
rename (i :< NeutPiElim e v) = do
  e' <- rename e
  v' <- rename v
  return $ i :< NeutPiElim e' v'
rename (i :< NeutSigma (x, t1) t2) = do
  t1' <- rename t1
  local $ do
    x' <- newNameWith x
    t2' <- rename t2
    return $ i :< NeutSigma (x', t1') t2' -- t' <- rename t
rename (i :< NeutSigmaIntro es) = do
  es' <- mapM rename es
  return $ i :< NeutSigmaIntro es'
rename (i :< NeutSigmaElim e1 xs e2) = do
  e1' <- rename e1
  local $ do
    xs' <- mapM newNameWith xs
    e2' <- rename e2
    return $ i :< NeutSigmaElim e1' xs' e2'
rename (i :< NeutBox t) = do
  t' <- rename t
  return $ i :< NeutBox t'
rename (i :< NeutBoxIntro t) = do
  t' <- rename t
  return $ i :< NeutBoxIntro t'
rename (i :< NeutBoxElim t) = do
  t' <- rename t
  return $ i :< NeutBoxElim t'
rename (i :< NeutIndex s) = return $ i :< NeutIndex s
rename (i :< NeutIndexIntro x) = return $ i :< NeutIndexIntro x
rename (i :< NeutIndexElim e branchList) = do
  e' <- rename e
  branchList' <- renameBranchList branchList
  return $ i :< NeutIndexElim e' branchList'
rename (i :< NeutConst t) = do
  t' <- rename t
  return $ i :< NeutConst t'
rename (i :< NeutConstIntro s) = return $ i :< NeutConstIntro s
rename (i :< NeutConstElim e) = do
  e' <- rename e
  return $ i :< NeutConstElim e'
rename (i :< NeutVector index t) = do
  index' <- rename index
  t' <- rename t
  return $ i :< NeutVector index' t'
rename (i :< NeutVectorIntro branchList) = do
  branchList' <- renameBranchList branchList
  return $ i :< NeutVectorIntro branchList'
rename (i :< NeutVectorElim e v) = do
  e' <- rename e
  v' <- rename v
  return $ i :< NeutVectorElim e' v'
rename (i :< NeutUniv j) = return $ i :< NeutUniv j
rename (i :< NeutMu s e) =
  local $ do
    s' <- newNameWith s
    e' <- rename e
    return $ i :< NeutMu s' e'
rename (i :< NeutHole x) = return $ i :< NeutHole x

renameBranchList :: [(IndexOrVar, Neut)] -> WithEnv [(IndexOrVar, Neut)]
renameBranchList branchList =
  forM branchList $ \(l, body) ->
    local $ do
      l' <- newNameIndex l
      body' <- rename body
      return (l', body')

newNameIndex :: IndexOrVar -> WithEnv IndexOrVar
newNameIndex (Right x) = do
  x' <- newNameWith x
  return $ Right x'
newNameIndex l = return l

local :: WithEnv a -> WithEnv a
local p = do
  env <- get
  x <- p
  modify (\e -> env {count = count e})
  return x
