module Lift
  ( lift
  ) where

import           Control.Comonad.Cofree
import           Control.Monad
import           Control.Monad.State        hiding (lift)
import           Control.Monad.Trans.Except

import           Data

lift :: Term -> WithEnv Term
lift v@(_ :< TermVar _) = return v
lift v@(_ :< TermConst _) = return v
lift (i :< TermLam arg body) = do
  body' <- lift body
  let freeVars = var body'
  newFormalArgs <- constructFormalArgs freeVars
  let freeToBound = zip freeVars newFormalArgs
  body'' <- replace freeToBound body'
  lam' <- bindFormalArgs newFormalArgs $ i :< TermLam arg body''
  args <- mapM wrapArg freeVars
  appFold lam' args
lift (i :< TermApp e v) = do
  e' <- lift e
  v' <- lift v
  return $ i :< TermApp e' v'
lift (i :< TermProduct v1 v2) = do
  v1' <- lift v1
  v2' <- lift v2
  return $ i :< TermProduct v1' v2'
lift (i :< TermThunk c) = do
  c' <- lift c
  return $ i :< TermThunk c'
lift (i :< TermUnthunk c) = do
  c' <- lift c
  return $ i :< TermUnthunk c'
lift (i :< TermLift v) = do
  v' <- lift v
  return $ i :< TermLift v'
lift (i :< TermBind s c1 c2) = do
  c1' <- lift c1
  c2' <- lift c2
  return $ i :< TermBind s c1' c2'
lift (meta :< TermMu s c) = do
  c' <- lift c
  return $ meta :< TermMu s c'
lift (i :< TermCase vs vcs) = do
  vs' <- mapM lift vs
  let (patList, bodyList) = unzip vcs
  bodyList' <- mapM lift bodyList
  return $ i :< TermCase vs' (zip patList bodyList')

replace :: [(Identifier, Identifier)] -> Term -> WithEnv Term
replace f2b (i :< TermVar s) =
  case lookup s f2b of
    Nothing -> return $ i :< TermVar s
    Just b -> do
      t <- lookupTypeEnv' i
      insTypeEnv b t
      return $ i :< TermVar b
replace _ v@(_ :< TermConst _) = return v
replace args (i :< TermThunk c) = do
  c' <- replace args c
  return $ i :< TermThunk c'
replace args (i :< TermLam x e) = do
  e' <- replace args e
  return $ i :< TermLam x e'
replace args (i :< TermApp e v) = do
  e' <- replace args e
  v' <- replace args v
  return $ i :< TermApp e' v'
replace args (i :< TermProduct v1 v2) = do
  v1' <- replace args v1
  v2' <- replace args v2
  return $ i :< TermProduct v1' v2'
replace args (i :< TermLift v) = do
  v' <- replace args v
  return $ i :< TermLift v'
replace args (i :< TermBind x e1 e2) = do
  e1' <- replace args e1
  e2' <- replace args e2
  return $ i :< TermBind x e1' e2'
replace args (i :< TermUnthunk v) = do
  v' <- replace args v
  return $ i :< TermUnthunk v'
replace args (i :< TermMu s c) = do
  c' <- replace args c
  return $ i :< TermMu s c'
replace args (i :< TermCase vs vcs) = do
  vs' <- mapM (replace args) vs
  let (patList, bodyList) = unzip vcs
  bodyList' <- mapM (replace args) bodyList
  return $ i :< TermCase vs' (zip patList bodyList')
