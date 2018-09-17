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

annotAsm :: Asm -> WithEnv Asm
annotAsm (meta :< AsmReturn x) = return $ meta {asmMetaUse = [x]} :< AsmReturn x
annotAsm (meta :< AsmMov x y cont) = do
  cont' <- annotAsm cont
  return $
    meta {asmMetaUse = varsInAsmArg y, asmMetaDef = [x]} :< AsmMov x y cont'
annotAsm (meta :< AsmLoadWithOffset offset base dest cont) = do
  cont' <- annotAsm cont
  return $
    meta {asmMetaUse = [base], asmMetaDef = [dest]} :<
    AsmLoadWithOffset offset base dest cont'
annotAsm (meta :< AsmStoreWithOffset val offset base cont) = do
  cont' <- annotAsm cont
  return $
    meta {asmMetaUse = base : varsInAsmArg val, asmMetaDef = []} :<
    AsmStoreWithOffset val offset base cont'
annotAsm (meta :< AsmCall x fun args cont) = do
  cont' <- annotAsm cont
  return $
    meta {asmMetaUse = fun : args, asmMetaDef = [x]} :< AsmCall x fun args cont'
annotAsm (meta :< AsmPush x cont) = do
  cont' <- annotAsm cont
  return $ meta {asmMetaDef = [x]} :< AsmPush x cont'
annotAsm (meta :< AsmPop x cont) = do
  cont' <- annotAsm cont
  return $ meta {asmMetaUse = [x]} :< AsmPop x cont'

varsInAsmArg :: AsmArg -> [Identifier]
varsInAsmArg (AsmArgReg x)       = [x]
varsInAsmArg (AsmArgImmediate _) = []

computeLiveness :: Asm -> WithEnv Asm
computeLiveness (meta :< AsmReturn x) = do
  contElems <- computeSuccAll (meta :< AsmReturn x)
  computeLiveness' meta contElems $ AsmReturn x
computeLiveness (meta :< AsmMov x y cont) = do
  cont' <- computeLiveness cont
  contElemList <- computeSuccAll (meta :< AsmMov x y cont')
  computeLiveness' meta contElemList (AsmMov x y cont')
computeLiveness (meta :< AsmLoadWithOffset x y i cont) = do
  cont' <- computeLiveness cont
  contElemList <- computeSuccAll (meta :< AsmLoadWithOffset x y i cont')
  computeLiveness' meta contElemList (AsmLoadWithOffset x y i cont')
computeLiveness (meta :< AsmStoreWithOffset x y i cont) = do
  cont' <- computeLiveness cont
  contElemList <- computeSuccAll (meta :< AsmStoreWithOffset x y i cont')
  computeLiveness' meta contElemList (AsmStoreWithOffset x y i cont')
computeLiveness (meta :< AsmCall x fun args cont) = do
  cont' <- computeLiveness cont
  contElemList <- computeSuccAll (meta :< AsmCall x fun args cont')
  computeLiveness' meta contElemList (AsmCall x fun args cont')
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
computeSuccAll (meta :< AsmLoadWithOffset _ _ _ cont) = do
  contLvs <- computeSuccAll cont
  return $ next meta contLvs
computeSuccAll (meta :< AsmStoreWithOffset _ _ _ cont) = do
  contLvs <- computeSuccAll cont
  return $ next meta contLvs
computeSuccAll (meta :< AsmCall _ _ _ cont) = do
  contLvs <- computeSuccAll cont
  return $ next meta contLvs
computeSuccAll (meta :< AsmPush _ cont) = do
  contLvs <- computeSuccAll cont
  return $ next meta contLvs
computeSuccAll (meta :< AsmPop _ cont) = do
  contLvs <- computeSuccAll cont
  return $ next meta contLvs
