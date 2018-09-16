module Liveness
  ( computeLiveness
  , annotAsm
  ) where

import           Data

import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.IORef

import           Control.Comonad.Cofree

import           Data.List

import           Debug.Trace

import qualified Text.Show.Pretty           as Pr

-- annotAsmEnv :: WithEnv ()
-- annotAsmEnv = do
--   env <- get
--   forM_ (codeEnv env) $ \(_, (_, asmRef)) -> do
--     asm <- liftIO $ readIORef asmRef
--     asm' <- annotAsm asm
--     liftIO $ writeIORef asmRef asm'
annotAsm :: Asm -> WithEnv Asm
annotAsm (meta :< AsmReturn x) = return $ meta {asmMetaUse = [x]} :< AsmReturn x
annotAsm (meta :< AsmMov x y cont) = do
  cont' <- annotAsm cont
  return $ meta {asmMetaUse = [y], asmMetaDef = [x]} :< AsmMov x y cont'
annotAsm (meta :< AsmCall x fun args cont) = do
  cont' <- annotAsm cont
  return $
    meta {asmMetaUse = fun : args, asmMetaDef = [x]} :< AsmCall x fun args cont'
annotAsm (meta :< AsmLoadAddr x addr cont) = do
  let used = varsInAddr addr
  return $ meta {asmMetaUse = used, asmMetaDef = [x]} :< AsmLoadAddr x addr cont
annotAsm (meta :< AsmPush x cont) = do
  cont' <- annotAsm cont
  return $ meta {asmMetaDef = [x]} :< AsmPush x cont'
annotAsm (meta :< AsmPop x cont) = do
  cont' <- annotAsm cont
  return $ meta {asmMetaUse = [x]} :< AsmPop x cont'

varsInAddr :: Addr -> [Identifier]
varsInAddr (AddrReg x)     = [x]
varsInAddr (AddrInt _)     = []
varsInAddr (AddrAdd a1 a2) = varsInAddr a1 ++ varsInAddr a2

-- livenessAnalysis :: WithEnv ()
-- livenessAnalysis = do
--   env <- get
--   forM_ (asmEnv env) $ \(_, (_, asmRef)) -> do
--     asm <- liftIO $ readIORef asmRef
--     asm' <- computeLiveness asm
--     liftIO $ writeIORef asmRef asm'
computeLiveness :: Asm -> WithEnv Asm
computeLiveness (meta :< AsmReturn x) = do
  contElems <- computeSuccAll (meta :< AsmReturn x)
  computeLiveness' meta contElems $ AsmReturn x
computeLiveness (meta :< AsmMov x y cont) = do
  cont' <- computeLiveness cont
  contElemList <- computeSuccAll (meta :< AsmMov x y cont')
  computeLiveness' meta contElemList (AsmMov x y cont')
computeLiveness (meta :< AsmCall x fun args cont) = do
  cont' <- computeLiveness cont
  contElemList <- computeSuccAll (meta :< AsmCall x fun args cont')
  computeLiveness' meta contElemList (AsmCall x fun args cont')
computeLiveness (meta :< AsmLoadAddr x addr cont) = do
  cont' <- computeLiveness cont
  contElemList <- computeSuccAll (meta :< AsmLoadAddr x addr cont')
  computeLiveness' meta contElemList (AsmLoadAddr x addr cont')
computeLiveness (meta :< AsmPush x cont) = do
  cont' <- computeLiveness cont
  contElemList <- computeSuccAll (meta :< AsmPush x cont')
  computeLiveness' meta contElemList (AsmPush x cont')
computeLiveness (meta :< AsmPop x cont) = do
  cont' <- computeLiveness cont
  contElemList <- computeSuccAll (meta :< AsmPop x cont')
  computeLiveness' meta contElemList (AsmPop x cont')

computeLiveness' :: AsmMeta -> [Identifier] -> AsmF Asm -> WithEnv Asm
computeLiveness' meta elems asm =
  if asmMetaLive meta /= elems
    then computeLiveness (meta {asmMetaLive = elems} :< asm)
    else return (meta :< asm)

computeCurrent' :: AsmMeta -> [Identifier]
computeCurrent' meta = do
  let lvs = asmMetaLive meta
  let dvs = asmMetaDef meta
  let uvs = asmMetaUse meta
  nub $ (lvs \\ dvs) ++ uvs

next :: AsmMeta -> [Identifier] -> [Identifier]
next meta lvs =
  nub $ computeCurrent' $ meta {asmMetaLive = asmMetaLive meta ++ lvs}

computeSuccAll :: Asm -> WithEnv [Identifier]
computeSuccAll (meta :< AsmReturn _) = return $ computeCurrent' meta
computeSuccAll (meta :< AsmMov _ _ cont) = do
  contLvs <- computeSuccAll cont
  return $ next meta contLvs
computeSuccAll (meta :< AsmCall _ _ _ cont) = do
  contLvs <- computeSuccAll cont
  return $ next meta contLvs
computeSuccAll (meta :< AsmLoadAddr _ _ cont) = do
  contLvs <- computeSuccAll cont
  return $ next meta contLvs
computeSuccAll (meta :< AsmPush _ cont) = do
  contLvs <- computeSuccAll cont
  return $ next meta contLvs
computeSuccAll (meta :< AsmPop _ cont) = do
  contLvs <- computeSuccAll cont
  return $ next meta contLvs
