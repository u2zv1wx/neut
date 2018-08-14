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
  forM_ (funEnv env) $ \(_, codeRef) -> do
    code <- liftIO $ readIORef codeRef
    code' <- annotCode code
    liftIO $ writeIORef codeRef code'

annotCode :: Code -> WithEnv Code
annotCode (meta :< (CodeReturn retReg label d)) = do
  uvs <- varsInData d
  return $ meta {codeMetaUse = retReg : uvs} :< CodeReturn retReg label d
annotCode (meta :< (CodeLet x d cont)) = do
  cont' <- annotCode cont
  uvs <- varsInData d
  dvs <- return [x]
  return $ meta {codeMetaUse = uvs, codeMetaDef = dvs} :< CodeLet x d cont'
annotCode (meta :< (CodeLetLink x d cont)) = do
  cont' <- annotCode cont
  uvs <- varsInData d
  dvs <- return [x]
  return $ meta {codeMetaUse = uvs, codeMetaDef = dvs} :< CodeLetLink x d cont'
annotCode (meta :< (CodeSwitch x defaultBranch branchList)) = do
  return $ meta {codeMetaUse = [x]} :< CodeSwitch x defaultBranch branchList
annotCode (meta :< (CodeJump labelName)) = do
  return $ meta :< CodeJump labelName
annotCode (meta :< (CodeRecursiveJump x)) = do
  return $ meta {codeMetaUse = [x]} :< CodeRecursiveJump x
annotCode (meta :< (CodeIndirectJump x unthunkId poss)) = do
  return $ meta {codeMetaUse = [x]} :< CodeIndirectJump x unthunkId poss
annotCode (meta :< (CodeStackSave stackReg cont)) = do
  cont' <- annotCode cont
  return $ meta {codeMetaUse = [stackReg]} :< CodeStackSave stackReg cont'
annotCode (meta :< (CodeStackRestore stackReg cont)) = do
  cont' <- annotCode cont
  return $ meta {codeMetaUse = [stackReg]} :< CodeStackRestore stackReg cont'

varsInData :: UData -> WithEnv [Identifier]
varsInData (Fix (DataPointer x)) = return [x]
varsInData (Fix (DataCell _ ds)) = do
  vss <- mapM varsInData ds
  return $ join vss
varsInData (Fix (DataLabel _)) = return []
varsInData (Fix (DataElemAtIndex d _)) = varsInData d

livenessAnalysis :: WithEnv ()
livenessAnalysis = do
  env <- get
  forM_ (funEnv env) $ \(_, codeRef) -> do
    code <- liftIO $ readIORef codeRef
    code' <- computeLiveness code
    liftIO $ writeIORef codeRef code'

computeLiveness :: Code -> WithEnv Code
computeLiveness (meta :< code@(CodeReturn _ _ _)) = do
  contElems <- computeSuccAll (meta :< code)
  computeLiveness' meta contElems code
computeLiveness (meta :< (CodeLet x d cont)) = do
  cont' <- computeLiveness cont
  contElemList <- computeSuccAll (meta :< (CodeLet x d cont'))
  computeLiveness' meta contElemList (CodeLet x d cont')
computeLiveness (meta :< (CodeLetLink x d cont)) = do
  cont' <- computeLiveness cont
  contElemList <- computeSuccAll (meta :< (CodeLetLink x d cont'))
  computeLiveness' meta contElemList (CodeLetLink x d cont')
computeLiveness (meta :< (CodeSwitch x defaultBranch branchList)) = do
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
    (CodeSwitch x defaultBranch branchList)
computeLiveness (meta :< (CodeJump labelName)) = do
  contRef <- lookupFunEnv labelName
  cont <- liftIO $ readIORef contRef
  cont' <- computeLiveness cont
  liftIO $ writeIORef contRef cont'
  contElemList <- computeSuccAll cont'
  computeLiveness' meta contElemList (CodeJump labelName)
computeLiveness (meta :< code@(CodeIndirectJump _ unthunkId poss)) = do
  contElemListList <-
    forM poss $ \thunkId -> do
      let label = "thunk" ++ thunkId ++ "unthunk" ++ unthunkId -- unthunkId
      codeRef <- lookupFunEnv label
      code <- liftIO $ readIORef codeRef
      code' <- computeLiveness code
      liftIO $ writeIORef codeRef code'
      computeSuccAll code'
  computeLiveness' meta (join contElemListList) code
computeLiveness (meta :< code@(CodeRecursiveJump _)) = do
  contElems <- computeSuccAll (meta :< code)
  computeLiveness' meta contElems code
computeLiveness (meta :< (CodeStackSave stackReg cont)) = do
  cont' <- computeLiveness cont
  contElemList <- computeSuccAll (meta :< (CodeStackSave stackReg cont'))
  computeLiveness' meta contElemList (CodeStackSave stackReg cont')
computeLiveness (meta :< (CodeStackRestore stackReg cont)) = do
  cont' <- computeLiveness cont
  contElemList <- computeSuccAll (meta :< (CodeStackRestore stackReg cont'))
  computeLiveness' meta contElemList (CodeStackRestore stackReg cont')

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
computeSuccAll (meta :< (CodeReturn _ _ _)) = do
  return $ computeCurrent' meta
computeSuccAll (meta :< (CodeLet _ _ cont)) = do
  contLvs <- computeSuccAll cont
  return $ next meta contLvs
computeSuccAll (meta :< (CodeLetLink _ _ cont)) = do
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
computeSuccAll (meta :< (CodeJump labelName)) = do
  cont <- lookupFunEnv labelName >>= liftIO . readIORef
  contElems <- computeSuccAll cont
  return $ next meta contElems
computeSuccAll (meta :< (CodeIndirectJump _ _ _)) = do
  return $ computeCurrent' meta
computeSuccAll (meta :< (CodeRecursiveJump _)) = do
  return $ computeCurrent' meta
computeSuccAll (meta :< (CodeStackSave _ cont)) = do
  contLvs <- computeSuccAll cont
  return $ next meta contLvs
computeSuccAll (meta :< (CodeStackRestore _ cont)) = do
  contLvs <- computeSuccAll cont
  return $ next meta contLvs
