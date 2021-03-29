module Clarify.Sigma
  ( immediateS4,
    returnImmediateS4,
    sigmaS4,
    returnClosureS4,
  )
where

import Clarify.Linearize
import Clarify.Utility
import Control.Monad.State.Lazy
import Data.Basic
import Data.Comp
import Data.Env
import qualified Data.Text as T

immediateName :: T.Text
immediateName =
  "cartesian-immediate"

returnImmediateS4 :: Hint -> WithEnv CompPlus
returnImmediateS4 m = do
  v <- immediateS4 m
  return (m, CompUpIntro v)

immediateS4 :: Hint -> WithEnv ValuePlus
immediateS4 m = do
  let immediateT _ = return (m, CompUpIntro (m, ValueSigmaIntro []))
  let immediate4 arg = return (m, CompUpIntro (m, ValueSigmaIntro [arg, arg]))
  tryCache m immediateName $ registerSwitcher m immediateName immediateT immediate4

sigmaS4 ::
  Maybe T.Text ->
  Hint ->
  [Either CompPlus (Ident, CompPlus)] ->
  WithEnv ValuePlus
sigmaS4 mName m mxts =
  case mName of
    Nothing -> do
      h <- toGlobalVarName <$> newIdentFromText "sigma"
      registerSwitcher m h (sigmaT m mxts) (sigma4 m mxts)
      return (m, ValueConst h)
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
  WithEnv CompPlus
sigmaT m mxts argVar = do
  xts <- mapM supplyName mxts
  -- as == [APP-1, ..., APP-n]   (`a` here stands for `app`)
  as <- forM xts $ \(x, t) -> toAffineApp m x t
  ys <- mapM (const $ newIdentFromText "arg") xts
  let body = bindLet (zip ys as) (m, CompUpIntro (m, ValueSigmaIntro []))
  body' <- linearize xts body
  return (m, CompSigmaElim False (map fst xts) argVar body')

-- (Assuming `ti` = `return di` for some `di` such that `xi : di`)
-- sigma4 NAME LOC [(x1, t1), ..., (xn, tn)]   ~>
--   update CompEnv with NAME ~> (thunk LAM), where LAM is:
--   lam z.
--     let (x1, ..., xn) := z in
--     <LINEARIZE_HEADER for x1, .., xn> in                                      ---
--     bind pair-1 :=                                                  ---       ---
--       bind f1 = t1 in              ---                              ---       ---
--       f1 @ (1, x1) in              ---  APP-1                       ---       ---
--     ...                                                             ---       ---
--     bind pair-n :=                                                  --- body  --- body'
--       bind fn = tn in              ---                              ---       ---
--       fn @ (1, xn) in              ---  APP-n                       ---       ---
--     let (p11, p12) := pair-1 in               ---                   ---       ---
--     ...                                       ---  TRANSPOSED-PAIR  ---       ---
--     let (pn1, pn2) := pair-n in               ---                   ---       ---
--     return ((p11, ..., pn1), (p12, ..., pn2)) ---                   ---       ---
sigma4 ::
  Hint ->
  [Either CompPlus (Ident, CompPlus)] ->
  ValuePlus ->
  WithEnv CompPlus
sigma4 m mxts argVar = do
  xts <- mapM supplyName mxts
  -- as == [APP-1, ..., APP-n]
  as <- forM xts $ \(x, t) -> toRelevantApp m x t
  -- pairVarNameList == [pair-1, ...,  pair-n]
  (pairVarNameList, pairVarTypeList) <- unzip <$> mapM toPairInfo xts
  transposedPair <- transposeSigma m pairVarTypeList
  let body = bindLet (zip pairVarNameList as) transposedPair
  body' <- linearize xts body
  return (m, CompSigmaElim False (map fst xts) argVar body')

toPairInfo :: (Ident, CompPlus) -> WithEnv (Ident, (ValuePlus, CompPlus))
toPairInfo (_, t@(m, _)) = do
  (name, var) <- newValueVarWith m "pair"
  return (name, (var, t))

-- transposeSigma [d1, ..., dn] :=
--   let (x1, y1) := d1 in
--   ...
--   let (xn, yn) := dn in
--   return ((x1, ..., xn), (y1, ..., yn))
transposeSigma :: Hint -> [(ValuePlus, CompPlus)] -> WithEnv CompPlus
transposeSigma m ds = do
  (xList, xVarList) <- unzip <$> mapM (const $ newValueVarWith m "sig-x") ds
  (yList, yVarList) <- unzip <$> mapM (const $ newValueVarWith m "sig-y") ds
  return $
    bindSigmaElim
      (zip (zip xList yList) ds)
      ( m,
        CompUpIntro
          ( m,
            ValueSigmaIntro
              [(m, ValueSigmaIntro xVarList), (m, ValueSigmaIntro yVarList)]
          )
      )

bindSigmaElim :: [((Ident, Ident), (ValuePlus, CompPlus))] -> CompPlus -> CompPlus
bindSigmaElim binder cont =
  case binder of
    [] ->
      cont
    ((x, y), (d, _)) : xyds ->
      (fst cont, CompSigmaElim False [x, y] d $ bindSigmaElim xyds cont)

supplyName :: Either b (Ident, b) -> WithEnv (Ident, b)
supplyName mName =
  case mName of
    Right (x, t) ->
      return (x, t)
    Left t -> do
      x <- newIdentFromText "unused-sigarg"
      return (x, t)

returnClosureS4 :: Hint -> WithEnv CompPlus
returnClosureS4 m = do
  (env, envVar) <- newValueVarWith m "env"
  retImmS4 <- returnImmediateS4 m
  t <-
    sigmaS4
      (Just "cartesian-closure")
      m
      [Right (env, retImmS4), Left (m, CompUpIntro envVar), Left retImmS4]
  return (m, CompUpIntro t)
