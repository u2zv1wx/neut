module Expand where

import           Control.Comonad.Cofree
import           Control.Monad
import           Control.Monad.State        hiding (expand)
import           Control.Monad.Trans.Except

import           Data

-- eliminate partial applications by eta-expansion
expand :: Neut -> WithEnv Neut
expand (i :< NeutVar x) = expand' 0 $ i :< NeutVar x
expand (i :< NeutPi (x, tdom) tcod) = do
  tdom' <- expand tdom
  tcod' <- expand tcod
  return $ i :< NeutPi (x, tdom') tcod'
expand (i :< NeutPiIntro arg body) = do
  body' <- expand body
  expand' 0 $ i :< NeutPiIntro arg body'
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
  expand' 0 $ i :< NeutSigmaElim e1' (x, y) e2'
expand (i :< NeutTop) = return $ i :< NeutTop
expand (i :< NeutTopIntro) = return $ i :< NeutTopIntro
expand (i :< NeutUniv j) = return $ i :< NeutUniv j
expand (i :< NeutHole x) = return $ i :< NeutHole x
expand (meta :< NeutMu s c) = do
  c' <- expand c
  expand' 0 $ meta :< NeutMu s c'

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
