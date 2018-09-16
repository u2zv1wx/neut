module Liveness
  ( annotCodeEnv
  , computeLiveness
  , livenessAnalysis
  ) where

import           Data

import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.IORef

import           Control.Comonad.Cofree

import           Data.List

import           Debug.Trace

import qualified Text.Show.Pretty           as Pr

annotCodeEnv :: WithEnv ()
annotCodeEnv = do
  env <- get
  forM_ (codeEnv env) $ \(_, (_, codeRef)) -> do
    code <- liftIO $ readIORef codeRef
    code' <- annotCode code
    liftIO $ writeIORef codeRef code'

annotCode :: Code -> WithEnv Code
annotCode (meta :< CodeReturn d) = do
  let uvs = varsInData d
  return $ meta {codeMetaUse = uvs} :< CodeReturn d
annotCode (meta :< CodeLet x d cont) = do
  cont' <- annotCode cont
  let uvs = varsInData d
  return $ meta {codeMetaUse = uvs, codeMetaDef = [x]} :< CodeLet x d cont'
annotCode (meta :< CodeCall x fun args cont) = do
  cont' <- annotCode cont
  let uvs1 = varsInData fun
  let uvs2 = concatMap varsInData args
  return $
    meta {codeMetaUse = uvs1 ++ uvs2, codeMetaDef = [x]} :<
    CodeCall x fun args cont'
annotCode (meta :< CodeExtractValue x base idx cont) = do
  cont' <- annotCode cont
  let uvs = varsInData base
  return $
    meta {codeMetaUse = uvs, codeMetaDef = [x]} :<
    CodeExtractValue x base idx cont'

varsInData :: Data -> [Identifier]
varsInData (DataLocal x)   = [x]
varsInData (DataGlobal x)  = [x]
varsInData DataNullPtr     = []
varsInData (DataStruct ds) = concatMap varsInData ds

livenessAnalysis :: WithEnv ()
livenessAnalysis = do
  env <- get
  forM_ (codeEnv env) $ \(_, (_, codeRef)) -> do
    code <- liftIO $ readIORef codeRef
    code' <- computeLiveness code
    liftIO $ writeIORef codeRef code'

computeLiveness :: Code -> WithEnv Code
computeLiveness (meta :< code@(CodeReturn _)) = do
  contElems <- computeSuccAll (meta :< code)
  computeLiveness' meta contElems code
computeLiveness (meta :< CodeLet x d cont) = do
  cont' <- computeLiveness cont
  contElemList <- computeSuccAll (meta :< CodeLet x d cont')
  computeLiveness' meta contElemList (CodeLet x d cont')
computeLiveness (meta :< CodeCall x fun args cont) = do
  cont' <- computeLiveness cont
  contElemList <- computeSuccAll (meta :< CodeCall x fun args cont')
  computeLiveness' meta contElemList (CodeCall x fun args cont')
computeLiveness (meta :< CodeExtractValue x base idx cont) = do
  cont' <- computeLiveness cont
  contElemList <- computeSuccAll (meta :< CodeExtractValue x base idx cont')
  computeLiveness' meta contElemList (CodeExtractValue x base idx cont')

computeLiveness' :: CodeMeta -> [Identifier] -> CodeF Code -> WithEnv Code
computeLiveness' meta elems code =
  if codeMetaLive meta /= elems
    then computeLiveness (meta {codeMetaLive = elems} :< code)
    else return (meta :< code)

computeCurrent' :: CodeMeta -> [Identifier]
computeCurrent' meta = do
  let lvs = codeMetaLive meta
  let dvs = codeMetaDef meta
  let uvs = codeMetaUse meta
  nub $ (lvs \\ dvs) ++ uvs

next :: CodeMeta -> [Identifier] -> [Identifier]
next meta lvs =
  nub $ computeCurrent' $ meta {codeMetaLive = codeMetaLive meta ++ lvs}

computeSuccAll :: Code -> WithEnv [Identifier]
computeSuccAll (meta :< CodeReturn _) = return $ computeCurrent' meta
computeSuccAll (meta :< CodeLet _ _ cont) = do
  contLvs <- computeSuccAll cont
  return $ next meta contLvs
computeSuccAll (meta :< CodeCall _ _ _ cont) = do
  contLvs <- computeSuccAll cont
  return $ next meta contLvs
computeSuccAll (meta :< CodeExtractValue _ _ _ cont) = do
  contLvs <- computeSuccAll cont
  return $ next meta contLvs
