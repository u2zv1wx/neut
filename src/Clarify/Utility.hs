module Clarify.Utility where

import Control.Monad.State.Lazy
import Data.Basic
import Data.Comp
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Namespace
import qualified Data.Text as T

toApp :: T.Text -> Hint -> Ident -> CompPlus -> Compiler CompPlus
toApp switcher m x t = do
  (expVarName, expVar) <- newValueVarLocalWith m "exp"
  return
    ( m,
      CompUpElim
        expVarName
        t
        ( m,
          CompPiElimDownElim
            expVar
            [(m, ValueEnumIntro switcher), (m, ValueVarLocal x)]
        )
    )

-- toAffineApp meta x t ~>
--   bind exp := t in
--   exp @ (0, x)
toAffineApp :: Hint -> Ident -> CompPlus -> Compiler CompPlus
toAffineApp =
  toApp boolFalse

-- toRelevantApp meta x t ~>
--   bind exp := t in
--   exp @ (1, x)
toRelevantApp :: Hint -> Ident -> CompPlus -> Compiler CompPlus
toRelevantApp =
  toApp boolTrue

bindLet :: [(Ident, CompPlus)] -> CompPlus -> CompPlus
bindLet binder cont =
  case binder of
    [] ->
      cont
    (x, e) : xes ->
      (fst e, CompUpElim x e $ bindLet xes cont)

switch :: CompPlus -> CompPlus -> [(EnumCase, CompPlus)]
switch e1 e2 =
  [(EnumCaseLabel boolFalse, e1), (EnumCaseDefault, e2)]

tryCache :: Hint -> T.Text -> Compiler () -> Compiler ValuePlus
tryCache m key doInsertion = do
  denv <- gets defEnv
  when (not $ Map.member key denv) doInsertion
  return (m, ValueVarGlobal key)

makeSwitcher ::
  Hint ->
  (ValuePlus -> Compiler CompPlus) ->
  (ValuePlus -> Compiler CompPlus) ->
  Compiler ([Ident], CompPlus)
makeSwitcher m compAff compRel = do
  (switchVarName, switchVar) <- newValueVarLocalWith m "switch"
  (argVarName, argVar) <- newValueVarLocalWith m "arg"
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

registerSwitcher ::
  Hint ->
  T.Text ->
  (ValuePlus -> Compiler CompPlus) ->
  (ValuePlus -> Compiler CompPlus) ->
  Compiler ()
registerSwitcher m name aff rel = do
  (args, e) <- makeSwitcher m aff rel
  insDefEnv name True args e

insDefEnv :: T.Text -> Bool -> [Ident] -> CompPlus -> Compiler ()
insDefEnv name isReducible args e =
  modify (\env -> env {defEnv = Map.insert name (isReducible, args, e) (defEnv env)})

{-# INLINE boolTrue #-}
boolTrue :: T.Text
boolTrue =
  "bool" <> nsSep <> "true"

{-# INLINE boolFalse #-}
boolFalse :: T.Text
boolFalse =
  "bool" <> nsSep <> "false"

{-# INLINE toGlobalVarName #-}
toGlobalVarName :: Ident -> T.Text
toGlobalVarName x =
  wrapWithQuote $ asText' x

{-# INLINE toConstructorLabelName #-}
toConstructorLabelName :: Ident -> T.Text
toConstructorLabelName x =
  wrapWithQuote $ asText x

{-# INLINE wrapWithQuote #-}
wrapWithQuote :: T.Text -> T.Text
wrapWithQuote x =
  "\"" <> x <> "\""
