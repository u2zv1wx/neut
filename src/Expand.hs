module Expand where

import           Control.Comonad.Cofree
import           Control.Monad
import           Control.Monad.State        hiding (expand)
import           Control.Monad.Trans.Except

import           Data

-- eliminate partial applications by eta-expansion
expand :: Neut -> WithEnv Neut
expand (i :< NeutVar x) = return $ i :< NeutVar x
expand (i :< NeutPi (x, tdom) tcod) = do
  tdom' <- expand tdom
  tcod' <- expand tcod
  return $ i :< NeutPi (x, tdom') tcod'
expand (i :< NeutPiIntro arg body) = do
  body' <- expand body
  return $ i :< NeutPiIntro arg body'
expand (i :< NeutPiElim e v) = do
  (fun, identArgList) <- funAndArgs (i :< NeutPiElim e v)
  let (identList, argList) = unzip identArgList
  argList' <- mapM expand argList
  expand' (length argList') $ coFunAndArgs (fun, zip identList argList')
expand (i :< NeutSigma (x, tdom) tcod) = do
  tdom' <- expand tdom
  tcod' <- expand tcod
  return $ i :< NeutSigma (x, tdom') tcod'
expand (i :< NeutSigmaIntro v1 v2) = do
  v1' <- expand v1
  v2' <- expand v2
  return $ i :< NeutSigmaIntro v1' v2'
expand (i :< NeutSigmaElim e1 (x, y) e2) = do
  e1' <- expand e1
  e2' <- expand e2
  return $ i :< NeutSigmaElim e1' (x, y) e2'
expand (i :< NeutBox e) = do
  e' <- expand e
  return $ i :< NeutBox e'
expand (i :< NeutBoxIntro e) = do
  e' <- expand e
  return $ i :< NeutBoxIntro e'
expand (i :< NeutBoxElim e) = do
  e' <- expand e
  return $ i :< NeutBoxElim e'
expand (i :< NeutIndex l) = return $ i :< NeutIndex l
expand (i :< NeutIndexIntro x) = return $ i :< NeutIndexIntro x
expand (i :< NeutIndexElim e branchList) = do
  e' <- expand e
  let (indexList, es) = unzip branchList
  es' <- mapM expand es
  return $ i :< NeutIndexElim e' (zip indexList es')
expand (i :< NeutUniv j) = return $ i :< NeutUniv j
expand (i :< NeutMu s c) = do
  c' <- expand c
  return $ i :< NeutMu s c'
expand (i :< NeutHole x) = return $ i :< NeutHole x

expand' :: Int -> Neut -> WithEnv Neut
expand' given term@(i :< _) = do
  t <- lookupTypeEnv' i
  case t of
    _ :< NeutPi _ _ -> do
      let (_, argTypeList) = forallArgs t
      let argList = map (\(x, _, _) -> x) argTypeList
      newArgList <- constructFormalArgs $ drop given argList
      termVarList <- mapM wrapArg newArgList
      term' <- appFold term termVarList
      bindFormalArgs newArgList term'
    _ -> return term
