module Clarify.Utility where

import Control.Monad.State.Lazy
import Data.Basic
import Data.Code
import Data.Env
import qualified Data.HashMap.Lazy as Map
import qualified Data.IntMap as IntMap
import Data.Term
import qualified Data.Text as T

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
    ( m,
      CodeUpElim
        expVarName
        t
        ( m,
          CodePiElimDownElim
            expVar
            [(m, DataEnumIntro (EnumValueIntS 64 0)), (m, DataUpsilon x)]
        )
    )

-- toRelevantApp meta x t ~>
--   bind exp := t in
--   exp @ (1, x)
--
toRelevantApp :: Meta -> Identifier -> CodePlus -> WithEnv CodePlus
toRelevantApp m x t = do
  (expVarName, expVar) <- newDataUpsilonWith m "rel-app-exp"
  return
    ( m,
      CodeUpElim
        expVarName
        t
        ( m,
          CodePiElimDownElim
            expVar
            [(m, DataEnumIntro (EnumValueIntS 64 1)), (m, DataUpsilon x)]
        )
    )

bindLet :: [(Identifier, CodePlus)] -> CodePlus -> CodePlus
bindLet [] cont = cont
bindLet ((x, e) : xes) cont = (fst e, CodeUpElim x e $ bindLet xes cont)

returnCartesianImmediate :: Meta -> WithEnv CodePlus
returnCartesianImmediate m = do
  v <- cartesianImmediate m
  return (m, CodeUpIntro v)

switch :: CodePlus -> CodePlus -> [(Case, CodePlus)]
switch e1 e2 = [(CaseValue (EnumValueIntS 64 0), e1), (CaseDefault, e2)]

cartImmName :: T.Text
cartImmName = "cartesian-immediate"

tryCache :: Meta -> T.Text -> WithEnv () -> WithEnv DataPlus
tryCache m key doInsertion = do
  cenv <- gets codeEnv
  when (not $ Map.member key cenv) $ doInsertion
  return (m, DataConst key)

makeSwitcher ::
  Meta ->
  (DataPlus -> WithEnv CodePlus) ->
  (DataPlus -> WithEnv CodePlus) ->
  WithEnv ([Identifier], CodePlus)
makeSwitcher m compAff compRel = do
  (switchVarName, switchVar) <- newDataUpsilonWith m "switch"
  (argVarName, argVar) <- newDataUpsilonWith m "argimm"
  aff <- compAff argVar
  rel <- compRel argVar
  return
    ( [switchVarName, argVarName],
      ( m,
        CodeEnumElim
          (IntMap.fromList [(asInt argVarName, argVar)])
          switchVar
          (switch aff rel)
      )
    )

cartesianImmediate :: Meta -> WithEnv DataPlus
cartesianImmediate m = do
  tryCache m cartImmName $ do
    (args, e) <- makeSwitcher m affineImmediate relevantImmediate
    insCodeEnv cartImmName args e

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
    (args, e) <- makeSwitcher m (affineStruct ks) (relevantStruct ks)
    insCodeEnv cartStructName args e

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
    ( m,
      CodeStructElim
        (zip xs ks)
        argVar
        ( m,
          CodeUpIntro
            (m, sigmaIntro [(m, DataStructIntro vks), (m, DataStructIntro vks)])
        )
    )

insCodeEnv :: T.Text -> [Identifier] -> CodePlus -> WithEnv ()
insCodeEnv name args e = do
  let def = Definition (IsFixed False) args e
  modify (\env -> env {codeEnv = Map.insert name def (codeEnv env)})
