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
rename (i :< NeutConst x) = return $ i :< NeutConst x
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
rename (i :< NeutSigma xts) = do
  xts' <- renameSigma xts
  return $ i :< NeutSigma xts'
rename (i :< NeutSigmaIntro es) = do
  es' <- mapM rename es
  return $ i :< NeutSigmaIntro es'
rename (i :< NeutSigmaElim e1 xs e2) = do
  e1' <- rename e1
  local $ do
    xs' <- mapM newNameWith xs
    e2' <- rename e2
    return $ i :< NeutSigmaElim e1' xs' e2'
rename (i :< NeutIndex s) = return $ i :< NeutIndex s
rename (i :< NeutIndexIntro x) = return $ i :< NeutIndexIntro x
rename (i :< NeutIndexElim e branchList) = do
  e' <- rename e
  branchList' <- renameBranchList branchList
  return $ i :< NeutIndexElim e' branchList'
rename (i :< NeutUniv j) = return $ i :< NeutUniv j
rename (i :< NeutMu s e) =
  local $ do
    s' <- newNameWith s
    e' <- rename e
    return $ i :< NeutMu s' e'
rename (i :< NeutHole x) = return $ i :< NeutHole x

renameSigma :: [(Identifier, Neut)] -> WithEnv [(Identifier, Neut)]
renameSigma [] = return []
renameSigma ((x, t):xts) = do
  t' <- rename t
  local $ do
    x' <- newNameWith x
    xts' <- renameSigma xts
    return $ (x', t') : xts'

renameBranchList :: [(Index, Neut)] -> WithEnv [(Index, Neut)]
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
