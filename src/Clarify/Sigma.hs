module Clarify.Sigma
  ( immediateS4,
    returnImmediateS4,
    closureEnvS4,
    returnClosureS4,
  )
where

import Clarify.Linearize
import Clarify.Utility
import Control.Monad
import Data.Basic
import Data.Comp
import Data.Global
import qualified Data.Text as T

immediateName :: T.Text
immediateName =
  "cartesian-immediate"

returnImmediateS4 :: Hint -> IO CompPlus
returnImmediateS4 m = do
  v <- immediateS4 m
  return (m, CompUpIntro v)

immediateS4 :: Hint -> IO ValuePlus
immediateS4 m = do
  let immediateT _ = return (m, CompUpIntro (m, ValueSigmaIntro []))
  let immediate4 arg = return (m, CompUpIntro arg)
  tryCache m immediateName $ registerSwitcher m immediateName immediateT immediate4

sigmaS4 ::
  Maybe T.Text ->
  Hint ->
  [Either CompPlus (Ident, CompPlus)] ->
  IO ValuePlus
sigmaS4 mName m mxts =
  case mName of
    Nothing -> do
      h <- wrapWithQuote <$> newText
      registerSwitcher m h (sigmaT m mxts) (sigma4 m mxts)
      return (m, ValueVarGlobal h)
    Just name ->
      tryCache m name $ registerSwitcher m name (sigmaT m mxts) (sigma4 m mxts)

-- (Assuming `ti` = `return di` for some `di` such that `xi : di`)
-- sigmaT NAME LOC [(x1, t1), ..., (xn, tn)]   ~>
--   update CompEnv with NAME ~> (thunk LAM), where LAM is:
--   lam z.
--     let (x1, ..., xn) := z in
--     <LINEARIZE_HEADER for x1, .., xn> in                     ---
--     bind y1 :=                                    ---        ---
--       bind f1 = t1 in              ---            ---        ---
--       f1 @ (0, x1) in              ---  APP-1     ---        ---
--     ...                                           ---  body  ---  body'
--     bind yn :=                                    ---        ---
--       bind fn = tn in              ---            ---        ---
--       fn @ (0, xn) in              ---  APP-n     ---        ---
--     return ()                                     ---        ---
--
sigmaT ::
  Hint ->
  [Either CompPlus (Ident, CompPlus)] ->
  ValuePlus ->
  IO CompPlus
sigmaT m mxts argVar = do
  xts <- mapM supplyName mxts
  -- as == [APP-1, ..., APP-n]   (`a` here stands for `app`)
  as <- forM xts $ \(x, t) -> toAffineApp m x t
  ys <- mapM (const $ newIdentFromText "arg") xts
  body' <- linearize xts $ bindLet (zip ys as) (m, CompUpIntro (m, ValueSigmaIntro []))
  return (m, CompSigmaElim False (map fst xts) argVar body')

-- (Assuming `ti` = `return di` for some `di` such that `xi : di`)
-- sigma4 NAME LOC [(x1, t1), ..., (xn, tn)]   ~>
--   update CompEnv with NAME ~> (thunk LAM), where LAM is:
--   lam z.
--     let-noetic (x1, ..., xn) := z in
--     <LINEARIZE_HEADER for x1, .., xn> in                                      ---
--     bind x1' :=                                                     ---       ---
--       bind f1 = t1 in              ---                              ---       ---
--       f1 @ (1, x1) in              ---  APP-1                       ---       ---
--     ...                                                             ---       ---
--     bind xn' :=                                                     --- body  --- body'
--       bind fn = tn in              ---                              ---       ---
--       fn @ (1, xn) in              ---  APP-n                       ---       ---
--     return (x1', ..., xn')
sigma4 ::
  Hint ->
  [Either CompPlus (Ident, CompPlus)] ->
  ValuePlus ->
  IO CompPlus
sigma4 m mxts argVar = do
  xts <- mapM supplyName mxts
  -- as == [APP-1, ..., APP-n]
  as <- forM xts $ \(x, t) -> toRelevantApp m x t
  (varNameList, varList) <- unzip <$> mapM (const $ newValueVarLocalWith m "pair") xts
  body' <- linearize xts $ bindLet (zip varNameList as) (m, CompUpIntro (m, ValueSigmaIntro varList))
  return (m, CompSigmaElim True (map fst xts) argVar body')

supplyName :: Either b (Ident, b) -> IO (Ident, b)
supplyName mName =
  case mName of
    Right (x, t) ->
      return (x, t)
    Left t -> do
      x <- newIdentFromText "unused-sigarg"
      return (x, t)

closureEnvS4 ::
  Hint ->
  [Either CompPlus (Ident, CompPlus)] ->
  IO ValuePlus
closureEnvS4 m mxts =
  case mxts of
    [] ->
      immediateS4 m -- performance optimization; not necessary for correctness
    _ ->
      sigmaS4 Nothing m mxts

returnClosureS4 :: Hint -> IO CompPlus
returnClosureS4 m = do
  (env, envVar) <- newValueVarLocalWith m "env"
  retImmS4 <- returnImmediateS4 m
  t <-
    sigmaS4
      (Just "cartesian-closure")
      m
      [Right (env, retImmS4), Left (m, CompUpIntro envVar), Left retImmS4]
  return (m, CompUpIntro t)
