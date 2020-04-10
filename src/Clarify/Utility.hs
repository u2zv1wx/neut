{-# LANGUAGE OverloadedStrings #-}

module Clarify.Utility where

import Control.Monad.State

import qualified Data.HashMap.Strict as Map
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Text as T

import Data.Basic
import Data.Code
import Data.Env
import Data.Term

type Context = [(Identifier, TermPlus)]

-- toAffineApp meta x t ~>
--   bind exp := t in
--   exp @ (0, x)
--
-- {} toAffineApp {}
toAffineApp :: Meta -> Identifier -> CodePlus -> WithEnv CodePlus
toAffineApp m x t = do
  (expVarName, expVar) <- newDataUpsilonWith m "aff-app-exp"
  return
    ( m
    , CodeUpElim
        expVarName
        t
        ( m
        , CodePiElimDownElim
            expVar
            [(m, DataEnumIntro (EnumValueIntS 64 0)), (m, DataUpsilon x)]))

-- toRelevantApp meta x t ~>
--   bind exp := t in
--   exp @ (1, x)
--
toRelevantApp :: Meta -> Identifier -> CodePlus -> WithEnv CodePlus
toRelevantApp m x t = do
  (expVarName, expVar) <- newDataUpsilonWith m "rel-app-exp"
  return
    ( m
    , CodeUpElim
        expVarName
        t
        ( m
        , CodePiElimDownElim
            expVar
            [(m, DataEnumIntro (EnumValueIntS 64 1)), (m, DataUpsilon x)]))

bindLet :: [(Identifier, CodePlus)] -> CodePlus -> CodePlus
bindLet [] cont = cont
bindLet ((x, e):xes) cont = (fst e, CodeUpElim x e $ bindLet xes cont)

returnCartesianImmediate :: Meta -> WithEnv CodePlus
returnCartesianImmediate m = do
  v <- cartesianImmediate m
  return (m, CodeUpIntro v)

toThetaInfo :: T.Text -> Meta -> WithEnv (T.Text, DataPlus)
toThetaInfo thetaName m = do
  i <- lookupConstNum thetaName
  let ident = asText' $ I (thetaName, i)
  return (ident, (m, DataTheta ident))

switch :: CodePlus -> CodePlus -> [(Case, CodePlus)]
switch e1 e2 = [(CaseValue (EnumValueIntS 64 0), e1), (CaseDefault, e2)]

cartesianImmediate :: Meta -> WithEnv DataPlus
cartesianImmediate m = do
  cenv <- gets codeEnv
  (ident, theta) <- toThetaInfo "cartesian-immediate" m
  case Map.lookup ident cenv of
    Just _ -> return theta
    Nothing -> do
      (switchVarName, switchVar) <- newDataUpsilonWith m "switch"
      (argVarName, argVar) <- newDataUpsilonWith m "argimm"
      aff <- affineImmediate argVar
      rel <- relevantImmediate argVar
      insCodeEnv
        ident
        [switchVarName, argVarName]
        ( m
        , CodeEnumElim
            (IntMap.fromList [(asInt argVarName, argVar)])
            switchVar
            (switch aff rel))
      return theta

affineImmediate :: DataPlus -> WithEnv CodePlus
affineImmediate (m, _) = return (m, CodeUpIntro (m, sigmaIntro []))

relevantImmediate :: DataPlus -> WithEnv CodePlus
relevantImmediate argVar@(m, _) =
  return (m, CodeUpIntro (m, sigmaIntro [argVar, argVar]))

cartesianStruct :: Meta -> [ArrayKind] -> WithEnv DataPlus
cartesianStruct m ks = do
  cenv <- gets codeEnv
  (ident, theta) <- toThetaInfo "cartesian-struct" m
  case Map.lookup ident cenv of
    Just _ -> return theta
    Nothing -> do
      (switchVarName, switchVar) <- newDataUpsilonWith m "switch"
      (argVarName, argVar) <- newDataUpsilonWith m "argstruct"
      aff <- affineStruct argVar ks
      rel <- relevantStruct argVar ks
      insCodeEnv
        ident
        [switchVarName, argVarName]
        ( m
        , CodeEnumElim
            (IntMap.fromList [(asInt argVarName, argVar)])
            switchVar
            (switch aff rel))
      return theta

affineStruct :: DataPlus -> [ArrayKind] -> WithEnv CodePlus
affineStruct argVar@(m, _) ks = do
  xs <- mapM (const $ newNameWith' "var") ks
  return
    (m, CodeStructElim (zip xs ks) argVar (m, CodeUpIntro (m, sigmaIntro [])))

relevantStruct :: DataPlus -> [ArrayKind] -> WithEnv CodePlus
relevantStruct argVar@(m, _) ks = do
  xs <- mapM (const $ newNameWith' "var") ks
  let vks = zip (map (\y -> (m, DataUpsilon y)) xs) ks
  return
    ( m
    , CodeStructElim
        (zip xs ks)
        argVar
        ( m
        , CodeUpIntro
            (m, sigmaIntro [(m, DataStructIntro vks), (m, DataStructIntro vks)])))

insCodeEnv :: T.Text -> [Identifier] -> CodePlus -> WithEnv ()
insCodeEnv name args e = do
  let def = Definition (IsFixed False) args e
  modify (\env -> env {codeEnv = Map.insert name def (codeEnv env)})
