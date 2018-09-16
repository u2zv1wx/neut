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
rename (i :< NeutForall (s, tdom) tcod) = do
  tdom' <- rename tdom
  local $ do
    s' <- newNameWith s
    tcod' <- rename tcod
    return $ i :< NeutForall (s', tdom') tcod'
rename (i :< NeutLam (s, tdom) e) = do
  tdom' <- rename tdom
  local $ do
    s' <- newNameWith s
    e' <- rename e
    return $ i :< NeutLam (s', tdom') e'
rename (i :< NeutApp e v) = do
  e' <- rename e
  v' <- rename v
  return $ i :< NeutApp e' v'
rename (i :< NeutPair v1 v2) = do
  v1' <- rename v1
  v2' <- rename v2
  return $ i :< NeutPair v1' v2'
rename (i :< NeutExists (s, tdom) tcod) = do
  tdom' <- rename tdom
  local $ do
    s' <- newNameWith s
    tcod' <- rename tcod
    return $ i :< NeutExists (s', tdom') tcod'
rename (i :< NeutMu s e) =
  local $ do
    s' <- newNameWith s
    e' <- rename e
    return $ i :< NeutMu s' e'
rename (i :< NeutCase e1 (x, y) e2) = do
  e1' <- rename e1
  local $ do
    x' <- newNameWith x
    y' <- newNameWith y
    e2' <- rename e2
    return $ i :< NeutCase e1' (x', y') e2'
rename (i :< NeutTop) = return $ i :< NeutTop
rename (i :< NeutUnit) = return $ i :< NeutUnit
rename (i :< NeutUniv) = return $ i :< NeutUniv
rename (i :< NeutHole x) = return $ i :< NeutHole x
