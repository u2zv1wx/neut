module Lift
  ( lift
  ) where

import           Control.Comonad.Cofree
import           Control.Monad
import           Control.Monad.State        hiding (lift)
import           Control.Monad.Trans.Except

import           Data

lift :: Neut -> WithEnv Neut
lift v@(_ :< NeutVar _) = return v
lift (i :< NeutForall (x, tdom) tcod) = do
  tdom' <- lift tdom
  tcod' <- lift tcod
  return $ i :< NeutForall (x, tdom') tcod'
lift (i :< NeutLam arg body) = do
  body' <- lift body
  let freeVars = var body'
  newFormalArgs <- constructFormalArgs freeVars
  let freeToBound = zip freeVars newFormalArgs
  body'' <- replace freeToBound body'
  lam' <- bindFormalArgs newFormalArgs $ i :< NeutLam arg body''
  args <- mapM wrapArg freeVars
  appFold lam' args
lift (i :< NeutApp e v) = do
  e' <- lift e
  v' <- lift v
  return $ i :< NeutApp e' v'
lift (i :< NeutExists (x, tdom) tcod) = do
  tdom' <- lift tdom
  tcod' <- lift tcod
  return $ i :< NeutExists (x, tdom') tcod'
lift (i :< NeutPair v1 v2) = do
  v1' <- lift v1
  v2' <- lift v2
  return $ i :< NeutPair v1' v2'
lift (i :< NeutCase e1 (x, y) e2) = do
  e1' <- lift e1
  e2' <- lift e2
  return $ i :< NeutCase e1' (x, y) e2'
lift (i :< NeutTop) = return $ i :< NeutTop
lift (i :< NeutUnit) = return $ i :< NeutUnit
lift (i :< NeutBottom) = return $ i :< NeutBottom
lift (i :< NeutAbort e) = do
  e' <- lift e
  return $ i :< NeutAbort e'
lift (i :< NeutUniv) = return $ i :< NeutUniv
lift (i :< NeutHole x) = return $ i :< NeutHole x
lift (meta :< NeutMu s c) = do
  c' <- lift c
  return $ meta :< NeutMu s c'

replace :: [(Identifier, Identifier)] -> Neut -> WithEnv Neut
replace f2b (i :< NeutVar s) =
  case lookup s f2b of
    Nothing -> return $ i :< NeutVar s
    Just b -> do
      t <- lookupTypeEnv' i
      insTypeEnv b t
      return $ i :< NeutVar b
replace args (i :< NeutForall (x, tdom) tcod) = do
  tdom' <- replace args tdom
  tcod' <- replace args tcod
  return $ i :< NeutForall (x, tdom') tcod'
replace args (i :< NeutLam x e) = do
  e' <- replace args e
  return $ i :< NeutLam x e'
replace args (i :< NeutApp e v) = do
  e' <- replace args e
  v' <- replace args v
  return $ i :< NeutApp e' v'
replace args (i :< NeutExists (x, tdom) tcod) = do
  tdom' <- replace args tdom
  tcod' <- replace args tcod
  return $ i :< NeutExists (x, tdom') tcod'
replace args (i :< NeutPair v1 v2) = do
  v1' <- replace args v1
  v2' <- replace args v2
  return $ i :< NeutPair v1' v2'
replace args (i :< NeutCase e1 (x, y) e2) = do
  e1' <- replace args e1
  e2' <- replace args e2
  return $ i :< NeutCase e1' (x, y) e2'
replace args (i :< NeutMu s c) = do
  c' <- replace args c
  return $ i :< NeutMu s c'
replace _ (i :< NeutTop) = return $ i :< NeutTop
replace _ (i :< NeutUnit) = return $ i :< NeutUnit
replace _ (i :< NeutBottom) = return $ i :< NeutBottom
replace args (i :< NeutAbort e) = do
  e' <- replace args e
  return $ i :< NeutAbort e'
replace _ (i :< NeutUniv) = return $ i :< NeutUniv
replace _ (i :< NeutHole x) = return $ i :< NeutHole x
