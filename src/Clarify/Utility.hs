{-# LANGUAGE OverloadedStrings #-}

module Clarify.Utility where

import Control.Monad.State

import Data.Basic
import Data.Code
import Data.Env
import Data.Term
import Reduce.Code

import qualified Data.HashMap.Strict as Map

type Context = [(Identifier, TermPlus)]

-- toAffineApp meta x t ~>
--   bind exp := t in
--   let (aff, rel) := exp in
--   aff @ x
--
-- {} toAffineApp {}
toAffineApp :: Meta -> Identifier -> CodePlus -> WithEnv CodePlus
toAffineApp m x t = do
  (expVarName, expVar) <- newDataUpsilonWith "aff-app-exp"
  (affVarName, affVar) <- newDataUpsilonWith "aff-app-aff"
  (relVarName, _) <- newDataUpsilonWith "aff-app-rel"
  retImmType <- returnCartesianImmediate
  return
    ( m
    , CodeUpElim
        expVarName
        t
        ( emptyMeta
        , CodeSigmaElim
            arrVoidPtr
            [(affVarName, retImmType), (relVarName, retImmType)]
            expVar
            (m, CodePiElimDownElim affVar [toDataUpsilon (x, m)])))

-- toRelevantApp meta x t ~>
--   bind exp := t in
--   let (aff, rel) := exp in
--   rel @ x
--
-- {} toRelevantApp {}
toRelevantApp :: Meta -> Identifier -> CodePlus -> WithEnv CodePlus
toRelevantApp m x t = do
  (expVarName, expVar) <- newDataUpsilonWith "rel-app-exp"
  (affVarName, _) <- newDataUpsilonWith "rel-app-aff"
  (relVarName, relVar) <- newDataUpsilonWith "rel-app-rel"
  retImmType <- returnCartesianImmediate
  return
    ( m
    , CodeUpElim
        expVarName
        t
        ( m
        , CodeSigmaElim
            arrVoidPtr
            [(affVarName, retImmType), (relVarName, retImmType)]
            expVar
            (m, CodePiElimDownElim relVar [toDataUpsilon (x, m)])))

-- {each x in xes is used linearly in cont} bindLet {each x in xes is used linearly in cont}
bindLet :: [(Identifier, CodePlus)] -> CodePlus -> CodePlus
bindLet [] cont = cont
bindLet ((x, e):xes) cont = (fst e, CodeUpElim x e $ bindLet xes cont)

returnUpsilon :: Identifier -> CodePlus
returnUpsilon x = (emptyMeta, CodeUpIntro (emptyMeta, DataUpsilon x))

-- {} returnCartesianImmediate {v is the aff-rel pair off imm}
returnCartesianImmediate :: WithEnv CodePlus
returnCartesianImmediate = do
  v <- cartesianImmediate emptyMeta
  return (emptyMeta, CodeUpIntro v)

-- {} returnCartesianUniv {v is the aff-rel pair of univ}
returnCartesianUniv :: WithEnv CodePlus
returnCartesianUniv = do
  v <- cartesianUniv emptyMeta
  return (emptyMeta, CodeUpIntro v)

cartesianImmediate :: Meta -> WithEnv DataPlus
cartesianImmediate m = do
  aff <- affineImmediate m
  rel <- relevantImmediate m
  return (m, DataSigmaIntro arrVoidPtr [aff, rel])

affineImmediate :: Meta -> WithEnv DataPlus
affineImmediate m = do
  cenv <- gets codeEnv
  let thetaName = "affine-immediate"
  let theta = (m, DataTheta thetaName)
  case Map.lookup thetaName cenv of
    Just _ -> return theta
    Nothing -> do
      immVarName <- newNameWith "arg"
      insCodeEnv
        thetaName
        [immVarName]
        (emptyMeta, CodeUpIntro (emptyMeta, DataSigmaIntro arrVoidPtr []))
      return theta

relevantImmediate :: Meta -> WithEnv DataPlus
relevantImmediate m = do
  cenv <- gets codeEnv
  let thetaName = "relevant-immediate"
  let theta = (m, DataTheta thetaName)
  case Map.lookup thetaName cenv of
    Just _ -> return theta
    Nothing -> do
      (immVarName, immVar) <- newDataUpsilonWith "arg"
      insCodeEnv
        thetaName
        [immVarName]
        ( emptyMeta
        , CodeUpIntro (emptyMeta, DataSigmaIntro arrVoidPtr [immVar, immVar]))
      return theta

cartesianUniv :: Meta -> WithEnv DataPlus
cartesianUniv m = do
  aff <- affineUniv m
  rel <- relevantUniv m
  return (m, DataSigmaIntro arrVoidPtr [aff, rel])

-- \x -> let (_, _) := x in unit
affineUniv :: Meta -> WithEnv DataPlus
affineUniv m = do
  cenv <- gets codeEnv
  let thetaName = "affine-univ"
  let theta = (m, DataTheta thetaName)
  case Map.lookup thetaName cenv of
    Just _ -> return theta
    Nothing -> do
      (univVarName, univVar) <- newDataUpsilonWith "univ"
      affVarName <- newNameWith "aff-univ"
      relVarName <- newNameWith "rel-univ"
      retImmType <- returnCartesianImmediate
      insCodeEnv
        thetaName
        [univVarName]
        -- let (a, b) := x in return ()
        ( emptyMeta
        , CodeSigmaElim
            arrVoidPtr
            [(affVarName, retImmType), (relVarName, retImmType)]
            univVar
            (emptyMeta, CodeUpIntro (emptyMeta, DataSigmaIntro arrVoidPtr [])))
      return theta

relevantUniv :: Meta -> WithEnv DataPlus
relevantUniv m = do
  cenv <- gets codeEnv
  let thetaName = "relevant-univ"
  let theta = (m, DataTheta thetaName)
  case Map.lookup thetaName cenv of
    Just _ -> return theta
    Nothing -> do
      (univVarName, univVar) <- newDataUpsilonWith "univ"
      (affVarName, affVar) <- newDataUpsilonWith "aff-univ"
      (relVarName, relVar) <- newDataUpsilonWith "rel-univ"
      retImmType <- returnCartesianImmediate
      insCodeEnv
        thetaName
        [univVarName]
        -- let (a, b) := x in return ((a, b), (a, b))
        ( emptyMeta
        , CodeSigmaElim
            arrVoidPtr
            [(affVarName, retImmType), (relVarName, retImmType)]
            univVar
            ( emptyMeta
            , CodeUpIntro
                ( emptyMeta
                , DataSigmaIntro
                    arrVoidPtr
                    [ (emptyMeta, DataSigmaIntro arrVoidPtr [affVar, relVar])
                    , (emptyMeta, DataSigmaIntro arrVoidPtr [affVar, relVar])
                    ])))
      return theta

cartesianStruct :: Meta -> [ArrayKind] -> WithEnv DataPlus
cartesianStruct m ks = do
  aff <- affineStruct m ks
  rel <- relevantStruct m ks
  return (m, DataSigmaIntro arrVoidPtr [aff, rel])

affineStruct :: Meta -> [ArrayKind] -> WithEnv DataPlus
affineStruct m ks = do
  cenv <- gets codeEnv
  let thetaName = "affine-struct"
  let theta = (m, DataTheta thetaName)
  case Map.lookup thetaName cenv of
    Just _ -> return theta
    Nothing -> do
      (structVarName, structVar) <- newDataUpsilonWith "struct"
      xs <- mapM (const $ newNameWith "var") ks
      insCodeEnv
        thetaName
        [structVarName]
        ( emptyMeta
        , CodeStructElim
            (zip xs ks)
            structVar
            (emptyMeta, CodeUpIntro (emptyMeta, DataSigmaIntro arrVoidPtr [])))
      return theta

relevantStruct :: Meta -> [ArrayKind] -> WithEnv DataPlus
relevantStruct m ks = do
  cenv <- gets codeEnv
  let thetaName = "relevant-struct"
  let theta = (m, DataTheta thetaName)
  case Map.lookup thetaName cenv of
    Just _ -> return theta
    Nothing -> do
      (structVarName, structVar) <- newDataUpsilonWith "struct"
      xs <- mapM (const $ newNameWith "var") ks
      let vs = map (\y -> (emptyMeta, DataUpsilon y)) xs
      let vks = zip vs ks
      insCodeEnv
        thetaName
        [structVarName]
        ( emptyMeta
        , CodeStructElim
            (zip xs ks)
            structVar
            ( emptyMeta
            , CodeUpIntro
                ( emptyMeta
                , DataSigmaIntro
                    arrVoidPtr
                    [ (emptyMeta, DataStructIntro vks)
                    , (emptyMeta, DataStructIntro vks)
                    ])))
      return theta

insCodeEnv :: Identifier -> [Identifier] -> CodePlus -> WithEnv ()
insCodeEnv name args e =
  modify (\env -> env {codeEnv = Map.insert name (args, e) (codeEnv env)})

lookupContext :: Identifier -> Context -> WithEnv TermPlus
lookupContext z ctx = do
  case lookup z ctx of
    Nothing -> throwError' "lookupContext"
    Just t -> return t

isClosedChain :: [(Identifier, CodePlus)] -> Bool
isClosedChain xts = null (isClosedChain' xts)

isClosedChain' :: [(Identifier, CodePlus)] -> [Identifier]
isClosedChain' [] = []
isClosedChain' ((x, t):xts) =
  varCode t ++ (filter ((/=) x) $ isClosedChain' xts)
