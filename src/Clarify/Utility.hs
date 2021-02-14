module Clarify.Utility where

import Control.Monad.State.Lazy
import Data.Comp
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

toApp :: T.Text -> Hint -> Ident -> CompPlus -> WithEnv CompPlus
toApp switcher m x t = do
  (expVarName, expVar) <- newValueUpsilonWith m "exp"
  return
    ( m,
      CompUpElim
        expVarName
        t
        ( m,
          CompPiElimDownElim
            expVar
            [(m, ValueEnumIntro switcher), (m, ValueUpsilon x)]
        )
    )

-- toAffineApp meta x t ~>
--   bind exp := t in
--   exp @ (0, x)
toAffineApp :: Hint -> Ident -> CompPlus -> WithEnv CompPlus
toAffineApp =
  toApp boolFalse

-- toRelevantApp meta x t ~>
--   bind exp := t in
--   exp @ (1, x)
toRelevantApp :: Hint -> Ident -> CompPlus -> WithEnv CompPlus
toRelevantApp =
  toApp boolTrue

bindLet :: [(Ident, CompPlus)] -> CompPlus -> CompPlus
bindLet binder cont =
  case binder of
    [] ->
      cont
    (x, e) : xes ->
      (fst e, CompUpElim x e $ bindLet xes cont)

returnCartesianImmediate :: Hint -> WithEnv CompPlus
returnCartesianImmediate m = do
  v <- cartesianImmediate m
  return (m, CompUpIntro v)

switch :: CompPlus -> CompPlus -> [(EnumCase, CompPlus)]
switch e1 e2 =
  [(EnumCaseLabel boolFalse, e1), (EnumCaseDefault, e2)]

cartImmName :: T.Text
cartImmName =
  "cartesian-immediate"

tryCache :: Hint -> T.Text -> WithEnv () -> WithEnv ValuePlus
tryCache m key doInsertion = do
  cenv <- gets codeEnv
  when (not $ Map.member key cenv) doInsertion
  return (m, ValueConst key)

makeSwitcher ::
  Hint ->
  (ValuePlus -> WithEnv CompPlus) ->
  (ValuePlus -> WithEnv CompPlus) ->
  WithEnv ([Ident], CompPlus)
makeSwitcher m compAff compRel = do
  (switchVarName, switchVar) <- newValueUpsilonWith m "switch"
  (argVarName, argVar) <- newValueUpsilonWith m "arg"
  aff <- compAff argVar
  rel <- compRel argVar
  return
    ( [switchVarName, argVarName],
      ( m,
        CompEnumElim
          switchVar
          (switch aff rel)
      )
    )

cartesianImmediate :: Hint -> WithEnv ValuePlus
cartesianImmediate m =
  tryCache m cartImmName $ do
    (args, e) <- makeSwitcher m affineImmediate relevantImmediate
    insCompEnv cartImmName False args e

affineImmediate :: ValuePlus -> WithEnv CompPlus
affineImmediate (m, _) =
  return (m, CompUpIntro (m, sigmaIntro []))

relevantImmediate :: ValuePlus -> WithEnv CompPlus
relevantImmediate argVar@(m, _) =
  return (m, CompUpIntro (m, sigmaIntro [argVar, argVar]))

cartesianStruct :: Hint -> [ArrayKind] -> WithEnv ValuePlus
cartesianStruct m ks = do
  (args, e) <- makeSwitcher m (affineStruct ks) (relevantStruct ks)
  i <- newCount
  let name = "cartesian-struct-" <> T.pack (show i)
  insCompEnv name False args e
  return (m, ValueConst name)

affineStruct :: [ArrayKind] -> ValuePlus -> WithEnv CompPlus
affineStruct ks argVar@(m, _) = do
  xs <- mapM (const $ newNameWith' "var") ks
  return
    (m, CompStructElim (zip xs ks) argVar (m, CompUpIntro (m, sigmaIntro [])))

relevantStruct :: [ArrayKind] -> ValuePlus -> WithEnv CompPlus
relevantStruct ks argVar@(m, _) = do
  xs <- mapM (const $ newNameWith' "var") ks
  let vks = zip (map (\y -> (m, ValueUpsilon y)) xs) ks
  return
    ( m,
      CompStructElim
        (zip xs ks)
        argVar
        ( m,
          CompUpIntro
            (m, sigmaIntro [(m, ValueStructIntro vks), (m, ValueStructIntro vks)])
        )
    )

insCompEnv :: T.Text -> Bool -> [Ident] -> CompPlus -> WithEnv ()
insCompEnv name isFixed args e = do
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
