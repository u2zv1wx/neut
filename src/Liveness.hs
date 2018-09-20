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
annotAsm (_ :< AsmReturn x) =
  return $ emptyAsmMeta {asmMetaUse = [x]} :< AsmReturn x
annotAsm (_ :< AsmLet x y cont) = do
  cont' <- annotAsm cont
  return $
    emptyAsmMeta {asmMetaUse = varsInAsmArg y, asmMetaDef = [x]} :<
    AsmLet x y cont'
annotAsm (_ :< AsmExtractValue dest (base, t) i cont) = do
  cont' <- annotAsm cont
  return $
    emptyAsmMeta {asmMetaUse = [base], asmMetaDef = [dest]} :<
    AsmExtractValue dest (base, t) i cont'
annotAsm (_ :< AsmInsertValue val (base, t) i cont) = do
  cont' <- annotAsm cont
  return $
    emptyAsmMeta {asmMetaUse = base : varsInAsmArg val} :<
    AsmInsertValue val (base, t) i cont'
annotAsm (_ :< AsmCall x fun args cont) = do
  cont' <- annotAsm cont
  return $
    emptyAsmMeta {asmMetaUse = fun : args, asmMetaDef = [x]} :<
    AsmCall x fun args cont'
annotAsm (_ :< AsmPush x cont) = do
  cont' <- annotAsm cont
  return $ emptyAsmMeta {asmMetaDef = [x]} :< AsmPush x cont'
annotAsm (_ :< AsmPop x cont) = do
  cont' <- annotAsm cont
  return $ emptyAsmMeta {asmMetaUse = [x]} :< AsmPop x cont'
annotAsm (_ :< AsmAddInt64 arg dest cont) = do
  cont' <- annotAsm cont
  return $
    emptyAsmMeta {asmMetaUse = varsInAsmArg arg, asmMetaDef = [dest]} :<
    AsmAddInt64 arg dest cont'
annotAsm (_ :< AsmSubInt64 arg dest cont) = do
  cont' <- annotAsm cont
  return $
    emptyAsmMeta {asmMetaUse = varsInAsmArg arg, asmMetaDef = [dest]} :<
    AsmSubInt64 arg dest cont'

computeLiveness :: Asm -> WithEnv Asm
computeLiveness (meta :< AsmReturn x) = do
  contElems <- computeSuccAll (meta :< AsmReturn x)
  computeLiveness' meta contElems $ AsmReturn x
computeLiveness (meta :< AsmLet x y cont) = do
  cont' <- computeLiveness cont
  contElemList <- computeSuccAll (meta :< AsmLet x y cont')
  computeLiveness' meta contElemList (AsmLet x y cont')
computeLiveness (meta :< AsmExtractValue x y i cont) = do
  cont' <- computeLiveness cont
  contElemList <- computeSuccAll (meta :< AsmExtractValue x y i cont')
  computeLiveness' meta contElemList (AsmExtractValue x y i cont')
computeLiveness (meta :< AsmInsertValue x y i cont) = do
  cont' <- computeLiveness cont
  contElemList <- computeSuccAll (meta :< AsmInsertValue x y i cont')
  computeLiveness' meta contElemList (AsmInsertValue x y i cont')
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
computeLiveness (meta :< AsmAddInt64 arg dest cont) = do
  cont' <- computeLiveness cont
  contElemList <- computeSuccAll (meta :< AsmAddInt64 arg dest cont')
  computeLiveness' meta contElemList (AsmAddInt64 arg dest cont')
computeLiveness (meta :< AsmSubInt64 arg dest cont) = do
  cont' <- computeLiveness cont
  contElemList <- computeSuccAll (meta :< AsmSubInt64 arg dest cont')
  computeLiveness' meta contElemList (AsmSubInt64 arg dest cont')

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
computeSuccAll (meta :< AsmLet _ _ cont) = do
  contLvs <- computeSuccAll cont
  return $ next meta contLvs
computeSuccAll (meta :< AsmExtractValue _ _ _ cont) = do
  contLvs <- computeSuccAll cont
  return $ next meta contLvs
computeSuccAll (meta :< AsmInsertValue _ _ _ cont) = do
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
computeSuccAll (meta :< AsmAddInt64 _ _ cont) = do
  contLvs <- computeSuccAll cont
  return $ next meta contLvs
computeSuccAll (meta :< AsmSubInt64 _ _ cont) = do
  contLvs <- computeSuccAll cont
  return $ next meta contLvs
