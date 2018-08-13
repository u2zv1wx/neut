module Liveness
  ( annotCodeEnv
  , computeLiveness
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
  forM_ (funEnv env) $ \(_, codeRef) -> do
    code <- liftIO $ readIORef codeRef
    code' <- annotCode code
    liftIO $ writeIORef codeRef code'

annotCode :: Code -> WithEnv Code
annotCode (meta :< (CodeReturn d)) = do
  uvs <- varsInData d
  return $ meta {codeMetaUse = uvs} :< CodeReturn d
annotCode (meta :< (CodeLet x d cont)) = do
  cont' <- annotCode cont
  uvs <- varsInData d
  dvs <- return [x]
  return $ meta {codeMetaUse = uvs, codeMetaDef = dvs} :< CodeLet x d cont'
annotCode (meta :< (CodeSwitch d defaultBranch branchList)) = do
  uvs <- varsInData d
  return $ meta {codeMetaUse = uvs} :< CodeSwitch d defaultBranch branchList
annotCode (meta :< (CodeCall x label argList cont)) = do
  cont' <- annotCode cont
  dvs <- return [x]
  uvs <- return argList
  return $
    meta {codeMetaUse = uvs, codeMetaDef = dvs} :<
    CodeCall x label argList cont'
annotCode (meta :< (CodeJump labelName argList)) = do
  uvs <- return argList
  return $ meta {codeMetaUse = uvs} :< CodeJump labelName argList
annotCode (meta :< (CodeStore x addr cont)) = do
  cont' <- annotCode cont
  dvs <- return [x]
  return $ meta {codeMetaDef = dvs} :< CodeStore x addr cont'
annotCode (meta :< (CodeLoad x addr cont)) = do
  cont' <- annotCode cont
  dvs <- return [x]
  return $ meta {codeMetaDef = dvs} :< CodeLoad x addr cont'

varsInData :: UData -> WithEnv [Identifier]
varsInData (Fix (DataPointer x)) = return [x]
varsInData (Fix (DataCell _ ds)) = do
  vss <- mapM varsInData ds
  return $ join vss
varsInData (Fix (DataLabel _)) = return []
varsInData (Fix (DataElemAtIndex d _)) = varsInData d

computeLiveness :: Code -> WithEnv Code
computeLiveness (meta :< code@(CodeReturn _)) = do
  contElems <- computeSuccAll (meta :< code)
  computeLiveness' meta contElems code
computeLiveness (meta :< (CodeLet x d cont)) = do
  cont' <- computeLiveness cont
  contElemList <- computeSuccAll (meta :< (CodeLet x d cont'))
  computeLiveness' meta contElemList (CodeLet x d cont')
computeLiveness (meta :< (CodeSwitch d defaultBranch branchList)) = do
  let labelList = defaultBranch : map snd branchList
  contElemListList <-
    forM labelList $ \label -> do
      contRef <- lookupFunEnv label
      cont <- liftIO $ readIORef contRef
      cont' <- computeLiveness cont
      liftIO $ writeIORef contRef cont'
      computeSuccAll cont'
  computeLiveness'
    meta
    (join contElemListList)
    (CodeSwitch d defaultBranch branchList)
computeLiveness (meta :< (CodeCall x label argList cont)) = do
  funRef <- lookupFunEnv label
  fun <- liftIO $ readIORef funRef
  fun' <- computeLiveness fun
  liftIO $ writeIORef funRef fun'
  funElemList <- computeSuccAll fun'
  cont' <- computeLiveness cont
  contElemList <- computeSuccAll cont'
  computeLiveness'
    meta
    (funElemList ++ contElemList)
    (CodeCall x label argList cont')
computeLiveness (meta :< (CodeJump labelName argList)) = do
  contRef <- lookupFunEnv labelName
  cont <- liftIO $ readIORef contRef
  cont' <- computeLiveness cont
  liftIO $ writeIORef contRef cont'
  contElemList <- computeSuccAll cont'
  computeLiveness' meta contElemList (CodeJump labelName argList)
computeLiveness (meta :< (CodeStore x d cont)) = do
  cont' <- computeLiveness cont
  contElemList <- computeSuccAll (meta :< (CodeStore x d cont'))
  computeLiveness' meta contElemList (CodeStore x d cont')
computeLiveness (meta :< (CodeLoad x d cont)) = do
  cont' <- computeLiveness cont
  contElemList <- computeSuccAll (meta :< (CodeLoad x d cont'))
  computeLiveness' meta contElemList (CodeLoad x d cont')

computeLiveness' :: CodeMeta -> [Identifier] -> PreCode -> WithEnv Code
computeLiveness' meta elems code =
  if codeMetaLive meta /= elems
    then computeLiveness (meta {codeMetaLive = elems} :< code)
    else return (meta :< code)

computeCurrent :: Code -> [Identifier]
computeCurrent (meta :< _) = computeCurrent' meta

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
computeSuccAll (meta :< (CodeReturn _)) = do
  return $ computeCurrent' meta
computeSuccAll (meta :< (CodeLet _ _ cont)) = do
  contLvs <- computeSuccAll cont
  return $ next meta contLvs
computeSuccAll (meta :< (CodeSwitch _ defaultBranch branchList)) = do
  let labelList = defaultBranch : map snd branchList
  contElemss <-
    forM labelList $ \label -> do
      contRef <- lookupFunEnv label
      cont <- liftIO $ readIORef contRef
      computeSuccAll cont
  return $ next meta (join contElemss)
computeSuccAll (meta :< (CodeCall _ label _ cont)) = do
  fun <- lookupFunEnv label >>= liftIO . readIORef
  funElems <- computeSuccAll fun
  contElems <- computeSuccAll cont
  return $ next meta (funElems ++ contElems)
computeSuccAll (meta :< (CodeJump labelName _)) = do
  cont <- lookupFunEnv labelName >>= liftIO . readIORef
  contElems <- computeSuccAll cont
  return $ next meta contElems
computeSuccAll (meta :< (CodeStore _ _ cont)) = do
  contLvs <- computeSuccAll cont
  return $ next meta contLvs
computeSuccAll (meta :< (CodeLoad _ _ cont)) = do
  contLvs <- computeSuccAll cont
  return $ next meta contLvs
