module Clarify.Utility where

import Control.Monad
import Data.Basic
import Data.Comp
import Data.Global
import qualified Data.HashMap.Lazy as Map
import Data.IORef
import Data.Namespace
import qualified Data.Text as T
import Path

toApp :: T.Text -> Hint -> Ident -> CompPlus -> IO CompPlus --
toApp switcher m x t = do
  (expVarName, expVar) <- newValueVarLocalWith m "exp"
  path <- getExecPath
  return
    ( m,
      CompUpElim
        expVarName
        t
        ( m,
          CompPiElimDownElim
            expVar
            [(m, ValueEnumIntro path switcher), (m, ValueVarLocal x)]
        )
    )

-- toAffineApp meta x t ~>
--   bind exp := t in
--   exp @ (0, x)
toAffineApp :: Hint -> Ident -> CompPlus -> IO CompPlus
toAffineApp =
  toApp boolFalse

-- toRelevantApp meta x t ~>
--   bind exp := t in
--   exp @ (1, x)
toRelevantApp :: Hint -> Ident -> CompPlus -> IO CompPlus
toRelevantApp =
  toApp boolTrue

bindLet :: [(Ident, CompPlus)] -> CompPlus -> CompPlus
bindLet binder cont =
  case binder of
    [] ->
      cont
    (x, e) : xes ->
      (fst e, CompUpElim x e $ bindLet xes cont)

switch :: Path Abs File -> CompPlus -> CompPlus -> [(EnumCase, CompPlus)]
switch path e1 e2 =
  -- [(EnumCaseInt 0, e1), (EnumCaseDefault, e2)]

  [(EnumCaseLabel path boolFalse, e1), (EnumCaseDefault, e2)]

tryCache :: Hint -> T.Text -> IO () -> IO ValuePlus
tryCache m key doInsertion = do
  denv <- readIORef defEnv
  when (not $ Map.member key denv) doInsertion
  return (m, ValueVarGlobal key)

makeSwitcher ::
  Hint ->
  (ValuePlus -> IO CompPlus) ->
  (ValuePlus -> IO CompPlus) ->
  IO ([Ident], CompPlus)
makeSwitcher m compAff compRel = do
  (switchVarName, switchVar) <- newValueVarLocalWith m "switch"
  (argVarName, argVar) <- newValueVarLocalWith m "arg"
  aff <- compAff argVar
  rel <- compRel argVar
  path <- getExecPath
  return
    ( [switchVarName, argVarName],
      ( m,
        CompEnumElim
          switchVar
          (switch path aff rel)
      )
    )

registerSwitcher ::
  Hint ->
  T.Text ->
  (ValuePlus -> IO CompPlus) ->
  (ValuePlus -> IO CompPlus) ->
  IO ()
registerSwitcher m name aff rel = do
  (args, e) <- makeSwitcher m aff rel
  insDefEnv name True args e

insDefEnv :: T.Text -> Bool -> [Ident] -> CompPlus -> IO ()
insDefEnv name isReducible args e =
  modifyIORef' defEnv $ \env -> Map.insert name (isReducible, args, e) env

{-# INLINE boolTrue #-}
boolTrue :: T.Text
boolTrue =
  "bool" <> nsSep <> "true"

{-# INLINE boolFalse #-}
boolFalse :: T.Text
boolFalse =
  "bool" <> nsSep <> "false"

{-# INLINE toGlobalVarName #-}
toGlobalVarName :: Path Abs File -> Ident -> T.Text
toGlobalVarName path x =
  wrapWithQuote $ asText x <> ";" <> T.pack (toFilePath path)

-- {-# INLINE toGlobalVarName #-}
-- toGlobalVarName :: Ident -> T.Text
-- toGlobalVarName x =
--   wrapWithQuote $ "neut:" <> asText x

{-# INLINE toConstructorLabelName #-}
toConstructorLabelName :: Ident -> T.Text
toConstructorLabelName x =
  wrapWithQuote $ asText x

{-# INLINE wrapWithQuote #-}
wrapWithQuote :: T.Text -> T.Text
wrapWithQuote x =
  "\"" <> x <> "\""
