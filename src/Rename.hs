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
rename (i :< NeutArrowIntro (s, tdom) e) = do
  tdom' <- renameType tdom
  local $ do
    s' <- newNameWith s
    e' <- rename e
    return $ i :< NeutArrowIntro (s', tdom') e'
rename (i :< NeutArrowElim e v) = do
  e' <- rename e
  v' <- rename v
  return $ i :< NeutArrowElim e' v'
rename (i :< NeutForallIntro s e) =
  local $ do
    s' <- newNameWith s
    e' <- rename e
    return $ i :< NeutForallIntro s' e'
rename (i :< NeutForallElim e v) = do
  e' <- rename e
  v' <- renameType v
  return $ i :< NeutForallElim e' v'
rename (i :< NeutPiIntro xs) = do
  xs' <-
    forM xs $ \(x, body) ->
      local $ do
        x' <- newNameWith x
        body' <- rename body
        return (x', body')
  return $ i :< NeutPiIntro xs'
rename (i :< NeutPiElim e1 e2) = do
  e1' <- rename e1
  e2' <- rename e2
  return $ i :< NeutPiElim e1' e2'
rename (i :< NeutProductIntro v1 v2) = do
  v1' <- rename v1
  v2' <- rename v2
  return $ i :< NeutProductIntro v1' v2'
rename (i :< NeutProductElim e1 (x, y) e2) = do
  e1' <- rename e1
  local $ do
    x' <- newNameWith x
    y' <- newNameWith y
    e2' <- rename e2
    return $ i :< NeutProductElim e1' (x', y') e2'
rename (i :< NeutExistsIntro x e) =
  local $ do
    x' <- newNameWith x
    e' <- rename e
    return $ i :< NeutExistsIntro x' e'
rename (i :< NeutExistsElim e1 (x, y) e2) = do
  e1' <- rename e1
  local $ do
    x' <- newNameWith x
    y' <- newNameWith y
    e2' <- rename e2
    return $ i :< NeutExistsElim e1' (x', y') e2'
rename (i :< NeutSigmaIntro e1 e2) = do
  e1' <- rename e1
  e2' <- rename e2
  return $ i :< NeutSigmaIntro e1' e2'
rename (i :< NeutSigmaElim e clauseList) = do
  e' <- rename e
  clauseList' <-
    forM clauseList $ \((li, xi), body) ->
      local $ do
        li' <- newNameWith li
        xi' <- newNameWith xi
        body' <- rename body
        return ((li', xi'), body')
  return $ i :< NeutSigmaElim e' clauseList'
rename (i :< NeutMu s e) =
  local $ do
    s' <- newNameWith s
    e' <- rename e
    return $ i :< NeutMu s' e'
rename (i :< NeutTopIntro) = return $ i :< NeutTopIntro

renameType :: WeakType -> WithEnv WeakType
renameType (WeakTypeVar s) = do
  WeakTypeVar <$> lookupNameEnv s
renameType (WeakTypeArrow t1 t2) = do
  t1' <- renameType t1
  t2' <- renameType t2
  return $ WeakTypeArrow t1' t2'
renameType (WeakTypeForall x t) =
  local $ do
    x' <- newNameWith x
    t' <- renameType t
    return $ WeakTypeForall x' t'
renameType (WeakTypePi xs) = do
  xs' <-
    forM xs $ \(li, ti) ->
      local $ do
        li' <- newNameWith li
        ti' <- renameType ti
        return (li', ti')
  return $ WeakTypePi xs'
renameType (WeakTypeProduct t1 t2) = do
  t1' <- renameType t1
  t2' <- renameType t2
  return $ WeakTypeProduct t1' t2'
renameType (WeakTypeExists x t) =
  local $ do
    x' <- newNameWith x
    t' <- renameType t
    return $ WeakTypeExists x' t'
renameType (WeakTypeSigma xs) = do
  xs' <-
    forM xs $ \(li, ti) ->
      local $ do
        li' <- newNameWith li
        ti' <- renameType ti
        return (li', ti')
  return $ WeakTypeSigma xs'
renameType WeakTypeTop = return WeakTypeTop
renameType (WeakTypeHole x) = return $ WeakTypeHole x
