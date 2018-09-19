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
rename (i :< NeutSigma (s, tdom) tcod) = do
  tdom' <- rename tdom
  local $ do
    s' <- newNameWith s
    tcod' <- rename tcod
    return $ i :< NeutSigma (s', tdom') tcod'
rename (i :< NeutSigmaIntro v1 v2) = do
  v1' <- rename v1
  v2' <- rename v2
  return $ i :< NeutSigmaIntro v1' v2'
rename (i :< NeutSigmaElim e1 (x, y) e2) = do
  e1' <- rename e1
  local $ do
    x' <- newNameWith x
    y' <- newNameWith y
    e2' <- rename e2
    return $ i :< NeutSigmaElim e1' (x', y') e2'
rename (i :< NeutMu s e) =
  local $ do
    s' <- newNameWith s
    e' <- rename e
    return $ i :< NeutMu s' e'
rename (i :< NeutTop) = return $ i :< NeutTop
rename (i :< NeutTopIntro) = return $ i :< NeutTopIntro
rename (i :< NeutUniv j) = return $ i :< NeutUniv j
rename (i :< NeutHole x) = return $ i :< NeutHole x
