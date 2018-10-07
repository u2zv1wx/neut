module Rename where

import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Control.Comonad.Cofree

import           Data

import qualified Text.Show.Pretty           as Pr

rename :: Neut -> WithEnv Neut
rename (i :< NeutVar s) = do
  t <- NeutVar <$> lookupNameEnv s
  return $ i :< t
rename (i :< NeutConst s t) = do
  t' <- rename t
  return $ i :< NeutConst s t'
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
rename (i :< NeutSigma [] tcod) = do
  tcod' <- rename tcod
  return $ i :< NeutSigma [] tcod'
rename (i :< NeutSigma ((x, t):xts) tcod) = do
  t' <- rename t
  local $ do
    x' <- newNameWith x
    _ :< NeutSigma xts' tcod' <- rename $ i :< NeutSigma xts tcod
    return $ i :< NeutSigma ((x', t') : xts') tcod'
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
  let (indexList, es) = unzip branchList
  es' <- mapM rename es
  return $ i :< NeutIndexElim e' (zip indexList es')
rename (i :< NeutUniv j) = return $ i :< NeutUniv j
rename (i :< NeutMu s e) =
  local $ do
    s' <- newNameWith s
    e' <- rename e
    return $ i :< NeutMu s' e'
rename (i :< NeutHole x) = return $ i :< NeutHole x

local :: WithEnv a -> WithEnv a
local p = do
  env <- get
  x <- p
  modify (\e -> env {count = count e})
  return x
