module Clarify.Utility where

import Control.Monad.State.Lazy
import Data.Code
import Data.EnumCase
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Hint
import Data.Ident
import Data.LowType
import Data.Namespace
import Data.Term
import qualified Data.Text as T

type Context = [(Ident, TermPlus)]

toApp :: T.Text -> Hint -> Ident -> CodePlus -> WithEnv CodePlus
toApp switcher m x t = do
  (expVarName, expVar) <- newDataUpsilonWith m "exp"
  return
    ( m,
      CodeUpElim
        expVarName
        t
        ( m,
          CodePiElimDownElim
            expVar
            [(m, DataEnumIntro switcher), (m, DataUpsilon x)]
        )
    )

-- toAffineApp meta x t ~>
--   bind exp := t in
--   exp @ (0, x)
toAffineApp :: Hint -> Ident -> CodePlus -> WithEnv CodePlus
toAffineApp =
  toApp boolFalse

-- toRelevantApp meta x t ~>
--   bind exp := t in
--   exp @ (1, x)
toRelevantApp :: Hint -> Ident -> CodePlus -> WithEnv CodePlus
toRelevantApp =
  toApp boolTrue

bindLet :: [(Ident, CodePlus)] -> CodePlus -> CodePlus
bindLet binder cont =
  case binder of
    [] ->
      cont
    (x, e) : xes ->
      (fst e, CodeUpElim x e $ bindLet xes cont)

returnCartesianImmediate :: Hint -> WithEnv CodePlus
returnCartesianImmediate m = do
  v <- cartesianImmediate m
  return (m, CodeUpIntro v)

switch :: CodePlus -> CodePlus -> [(EnumCase, CodePlus)]
switch e1 e2 =
  [(EnumCaseLabel boolFalse, e1), (EnumCaseDefault, e2)]

cartImmName :: T.Text
cartImmName =
  "cartesian-immediate"

tryCache :: Hint -> T.Text -> WithEnv () -> WithEnv DataPlus
tryCache m key doInsertion = do
  cenv <- gets codeEnv
  when (not $ Map.member key cenv) doInsertion
  return (m, DataConst key)

makeSwitcher ::
  Hint ->
  (DataPlus -> WithEnv CodePlus) ->
  (DataPlus -> WithEnv CodePlus) ->
  WithEnv ([Ident], CodePlus)
makeSwitcher m compAff compRel = do
  (switchVarName, switchVar) <- newDataUpsilonWith m "switch"
  (argVarName, argVar) <- newDataUpsilonWith m "arg"
  aff <- compAff argVar
  rel <- compRel argVar
  return
    ( [switchVarName, argVarName],
      ( m,
        CodeEnumElim
          switchVar
          (switch aff rel)
      )
    )

cartesianImmediate :: Hint -> WithEnv DataPlus
cartesianImmediate m =
  tryCache m cartImmName $ do
    (args, e) <- makeSwitcher m affineImmediate relevantImmediate
    insCodeEnv cartImmName False args e

affineImmediate :: DataPlus -> WithEnv CodePlus
affineImmediate (m, _) =
  return (m, CodeUpIntro (m, sigmaIntro []))

relevantImmediate :: DataPlus -> WithEnv CodePlus
relevantImmediate argVar@(m, _) =
  return (m, CodeUpIntro (m, sigmaIntro [argVar, argVar]))

cartesianStruct :: Hint -> [ArrayKind] -> WithEnv DataPlus
cartesianStruct m ks = do
  (args, e) <- makeSwitcher m (affineStruct ks) (relevantStruct ks)
  i <- newCount
  let name = "cartesian-struct-" <> T.pack (show i)
  insCodeEnv name False args e
  return (m, DataConst name)

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

insCodeEnv :: T.Text -> Bool -> [Ident] -> CodePlus -> WithEnv ()
insCodeEnv name isFixed args e = do
  let def = Definition (IsFixed isFixed) args e
  modify (\env -> env {codeEnv = Map.insert name def (codeEnv env)})

{-# INLINE boolTrue #-}
boolTrue :: T.Text
boolTrue =
  "bool" <> nsSep <> "true"

{-# INLINE boolFalse #-}
boolFalse :: T.Text
boolFalse =
  "bool" <> nsSep <> "false"
