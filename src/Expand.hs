module Expand where

import           Control.Comonad.Cofree
import           Control.Monad
import           Control.Monad.State        hiding (lift)
import           Control.Monad.Trans.Except

import           Data

-- eliminate partial applications by eta-expansion
expand :: Term -> WithEnv Term
expand (i :< TermVar x) = expand' 0 $ i :< TermVar x
expand (i :< TermThunk c) = do
  c' <- expand c
  expand' 0 $ i :< TermThunk c'
expand (i :< TermLam arg body) = do
  body' <- expand body
  expand' 0 $ i :< TermLam arg body'
expand (i :< TermApp e v) = do
  (fun, identArgList) <- funAndArgs (i :< TermApp e v)
  let (identList, argList) = unzip identArgList
  argList' <- mapM expand argList
  expand' (length argList') $ coFunAndArgs (fun, zip identList argList')
expand (i :< TermLift v) = do
  v' <- expand v
  expand' 0 $ i :< TermLift v'
expand (i :< TermBind x e1 e2) = do
  e1' <- expand e1
  e2' <- expand e2
  expand' 0 $ i :< TermBind x e1' e2'
expand (i :< TermUnthunk v) = do
  v' <- expand v
  expand' 0 $ i :< TermUnthunk v'
expand (meta :< TermMu s c) = do
  c' <- expand c
  expand' 0 $ meta :< TermMu s c'
expand (i :< TermCase vs vcs) = do
  vs' <- mapM expand vs
  let (patList, bodyList) = unzip vcs
  bodyList' <- mapM expand bodyList
  expand' 0 $ i :< TermCase vs' (zip patList bodyList')
expand _ = error "Expand.expand: illegal argument"

expand' :: Int -> Term -> WithEnv Term
expand' given term@(i :< _) = do
  t <- lookupTypeEnv' i
  case t of
    Fix (TypeForall _ _) -> do
      let (_, argTypeList) = forallArgs t
      let argList = map fst argTypeList
      newArgList <- constructFormalArgs $ drop given argList
      termVarList <- mapM wrapArg newArgList
      term' <- appFold term termVarList
      bindFormalArgs newArgList term'
    _ -> return term
