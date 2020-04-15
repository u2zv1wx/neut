{-# LANGUAGE OverloadedStrings #-}

module Clarify.Utility where

import Control.Monad.State

import qualified Data.HashMap.Strict as Map
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Set as S
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

newConstInfo :: T.Text -> Meta -> WithEnv (T.Text, DataPlus)
newConstInfo name m = do
  time <- gets timestamp
  i <- newCount
  let name' = "_" <> T.pack (show time) <> "-" <> name <> "-" <> T.pack (show i)
  return (name', (m, DataConst name'))

switch :: CodePlus -> CodePlus -> [(Case, CodePlus)]
switch e1 e2 = [(CaseValue (EnumValueIntS 64 0), e1), (CaseDefault, e2)]

cartImmName :: T.Text
cartImmName = "cartesian-immediate"

nameDefinition :: Meta -> T.Text -> Definition -> WithEnv DataPlus
nameDefinition m key def = do
  (name, theta) <- newConstInfo key m
  insCodeEnv' name def
  modify (\env -> env {inlineSet = S.insert name (inlineSet env)})
  return theta

tryCache :: Meta -> T.Text -> WithEnv DataPlus -> WithEnv DataPlus
tryCache m key f = do
  scenv <- gets sharedCodeEnv
  case Map.lookup key scenv of
    Nothing -> f
    Just def -> do
      nameDefinition m key def

makeSwitcher ::
     Meta
  -> (DataPlus -> WithEnv CodePlus)
  -> (DataPlus -> WithEnv CodePlus)
  -> WithEnv Definition
makeSwitcher m compAff compRel = do
  (switchVarName, switchVar) <- newDataUpsilonWith m "switch"
  (argVarName, argVar) <- newDataUpsilonWith m "argimm"
  aff <- compAff argVar
  rel <- compRel argVar
  return $
    Definition
      (IsFixed False)
      [switchVarName, argVarName]
      ( m
      , CodeEnumElim
          (IntMap.fromList [(asInt argVarName, argVar)])
          switchVar
          (switch aff rel))

cartesianImmediate :: Meta -> WithEnv DataPlus
cartesianImmediate m = do
  tryCache m cartImmName $ do
    def <- makeSwitcher m affineImmediate relevantImmediate
    insSharedCodeEnv' cartImmName def
    cartesianImmediate m

affineImmediate :: DataPlus -> WithEnv CodePlus
affineImmediate (m, _) = return (m, CodeUpIntro (m, sigmaIntro []))

relevantImmediate :: DataPlus -> WithEnv CodePlus
relevantImmediate argVar@(m, _) =
  return (m, CodeUpIntro (m, sigmaIntro [argVar, argVar]))

cartStructName :: T.Text
cartStructName = "cartesian-struct"

cartesianStruct :: Meta -> [ArrayKind] -> WithEnv DataPlus
cartesianStruct m ks = do
  tryCache m cartStructName $ do
    def <- makeSwitcher m (affineStruct ks) (relevantStruct ks)
    insSharedCodeEnv' cartStructName def
    cartesianStruct m ks

affineStruct :: [ArrayKind] -> DataPlus -> WithEnv CodePlus
affineStruct ks argVar@(m, _) = do
  xs <- mapM (const $ newNameWith' "var") ks
  return
    (m, CodeStructElim (zip xs ks) argVar (m, CodeUpIntro (m, sigmaIntro [])))

relevantStruct :: [ArrayKind] -> DataPlus -> WithEnv CodePlus
relevantStruct ks argVar@(m, _) = do
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

insCodeEnv' :: T.Text -> Definition -> WithEnv ()
insCodeEnv' name def = do
  modify (\env -> env {codeEnv = Map.insert name def (codeEnv env)})

insSharedCodeEnv :: T.Text -> [Identifier] -> CodePlus -> WithEnv ()
insSharedCodeEnv name args e = do
  let def = Definition (IsFixed False) args e
  modify (\env -> env {sharedCodeEnv = Map.insert name def (sharedCodeEnv env)})

insSharedCodeEnv' :: T.Text -> Definition -> WithEnv ()
insSharedCodeEnv' name def = do
  modify (\env -> env {sharedCodeEnv = Map.insert name def (sharedCodeEnv env)})
