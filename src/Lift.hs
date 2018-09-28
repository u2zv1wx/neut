module Lift
  ( lift
  ) where

import           Control.Comonad.Cofree
import           Control.Monad
import           Control.Monad.State        hiding (lift)
import           Control.Monad.Trans.Except

import qualified Text.Show.Pretty           as Pr

import           Data

lift :: Neut -> WithEnv Neut
lift v@(_ :< NeutVar _) = return v
lift (i :< NeutPi (x, tdom) tcod) = do
  tdom' <- lift tdom
  tcod' <- lift tcod
  return $ i :< NeutPi (x, tdom') tcod'
lift (i :< NeutPiIntro arg body) = do
  body' <- lift body
  freeVars <- var $ i :< NeutPiIntro arg body'
  newFormalArgs <- constructFormalArgs freeVars
  let freeToBound = zip freeVars newFormalArgs
  body'' <- replace freeToBound body'
  lam' <- bindFormalArgs newFormalArgs $ i :< NeutPiIntro arg body''
  args <- mapM wrapArg freeVars
  appFold lam' args
lift (i :< NeutPiElim e v) = do
  e' <- lift e
  v' <- lift v
  return $ i :< NeutPiElim e' v'
lift (i :< NeutSigma (x, tdom) tcod) = do
  tdom' <- lift tdom
  tcod' <- lift tcod
  return $ i :< NeutSigma (x, tdom') tcod'
lift (i :< NeutSigmaIntro v1 v2) = do
  v1' <- lift v1
  v2' <- lift v2
  return $ i :< NeutSigmaIntro v1' v2'
lift (i :< NeutSigmaElim e1 (x, y) e2) = do
  e1' <- lift e1
  e2' <- lift e2
  return $ i :< NeutSigmaElim e1' (x, y) e2'
lift (i :< NeutBox e) = do
  e' <- lift e
  return $ i :< NeutBox e'
lift (i :< NeutBoxIntro e) = do
  e' <- lift e
  return $ i :< NeutBoxIntro e'
lift (i :< NeutBoxElim e) = do
  e' <- lift e
  return $ i :< NeutBoxElim e'
lift (i :< NeutIndex l) = return $ i :< NeutIndex l
lift (i :< NeutIndexIntro x) = return $ i :< NeutIndexIntro x
lift (i :< NeutIndexElim e branchList) = do
  e' <- lift e
  let (indexList, es) = unzip branchList
  es' <- mapM lift es
  return $ i :< NeutIndexElim e' (zip indexList es')
lift (i :< NeutUniv j) = return $ i :< NeutUniv j
lift (i :< NeutMu s c) = do
  c' <- lift c
  return $ i :< NeutMu s c'
lift (i :< NeutHole x) = return $ i :< NeutHole x

replace :: [(Identifier, Identifier)] -> Neut -> WithEnv Neut
replace f2b (i :< NeutVar s) =
  case lookup s f2b of
    Nothing -> return $ i :< NeutVar s
    Just b -> do
      t <- lookupTypeEnv' i
      insTypeEnv b t
      return $ i :< NeutVar b
replace args (i :< NeutPi (x, tdom) tcod) = do
  tdom' <- replace args tdom
  tcod' <- replace args tcod
  return $ i :< NeutPi (x, tdom') tcod'
replace args (i :< NeutPiIntro x e) = do
  e' <- replace args e
  return $ i :< NeutPiIntro x e'
replace args (i :< NeutPiElim e v) = do
  e' <- replace args e
  v' <- replace args v
  return $ i :< NeutPiElim e' v'
replace args (i :< NeutSigma (x, tdom) tcod) = do
  tdom' <- replace args tdom
  tcod' <- replace args tcod
  return $ i :< NeutSigma (x, tdom') tcod'
replace args (i :< NeutSigmaIntro v1 v2) = do
  v1' <- replace args v1
  v2' <- replace args v2
  return $ i :< NeutSigmaIntro v1' v2'
replace args (i :< NeutSigmaElim e1 (x, y) e2) = do
  e1' <- replace args e1
  e2' <- replace args e2
  return $ i :< NeutSigmaElim e1' (x, y) e2'
replace args (i :< NeutBox e) = do
  e' <- replace args e
  return $ i :< NeutBox e'
replace args (i :< NeutBoxIntro e) = do
  e' <- replace args e
  return $ i :< NeutBoxIntro e'
replace args (i :< NeutBoxElim e) = do
  e' <- replace args e
  return $ i :< NeutBoxElim e'
replace _ (i :< NeutIndex l) = return $ i :< NeutIndex l
replace _ (i :< NeutIndexIntro x) = return $ i :< NeutIndexIntro x
replace args (i :< NeutIndexElim e branchList) = do
  e' <- replace args e
  let (indexList, es) = unzip branchList
  es' <- mapM (replace args) es
  return $ i :< NeutIndexElim e' (zip indexList es')
replace _ (i :< NeutUniv j) = return $ i :< NeutUniv j
replace args (i :< NeutMu s c) = do
  c' <- replace args c
  return $ i :< NeutMu s c'
replace _ (i :< NeutHole x) = return $ i :< NeutHole x
