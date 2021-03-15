module Clarify.Utility where

import Control.Monad.State.Lazy
import Data.Basic
import Data.Comp
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Namespace
import qualified Data.Text as T

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

switch :: CompPlus -> CompPlus -> [(EnumCase, CompPlus)]
switch e1 e2 =
  [(EnumCaseLabel boolFalse, e1), (EnumCaseDefault, e2)]

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

registerSwitcher ::
  Hint ->
  T.Text ->
  (ValuePlus -> WithEnv CompPlus) ->
  (ValuePlus -> WithEnv CompPlus) ->
  WithEnv ()
registerSwitcher m name aff rel = do
  (args, e) <- makeSwitcher m aff rel
  insCompEnv name False args e

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

{-# INLINE toGlobalVarName #-}
toGlobalVarName :: Ident -> T.Text
toGlobalVarName x =
  "_" <> T.pack (show (asInt x))
