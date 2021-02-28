module Clarify.Sigma
  ( cartesianSigma,
    returnClosureType,
  )
where

import Clarify.Linearize
import Clarify.Utility
import Control.Monad.State.Lazy
import Data.Basic
import Data.Comp
import Data.Env
import qualified Data.Text as T

cartesianSigma ::
  Maybe T.Text ->
  Hint ->
  [Either CompPlus (Ident, CompPlus)] ->
  WithEnv ValuePlus
cartesianSigma mName m mxts =
  case mName of
    Nothing -> do
      (args, e) <- makeSwitcher m (affineSigma m mxts) (relevantSigma m mxts)
      i <- newCount
      let h = "sigma-" <> T.pack (show i)
      insCompEnv h False args e
      return (m, ValueConst h)
    Just name ->
      tryCache m name $ do
        (args, e) <- makeSwitcher m (affineSigma m mxts) (relevantSigma m mxts)
        insCompEnv name False args e

-- (Assuming `ti` = `return di` for some `di` such that `xi : di`)
-- affineSigma NAME LOC [(x1, t1), ..., (xn, tn)]   ~>
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
affineSigma ::
  Hint ->
  [Either CompPlus (Ident, CompPlus)] ->
  ValuePlus ->
  WithEnv CompPlus
affineSigma m mxts argVar = do
  xts <- mapM supplyName mxts
  -- as == [APP-1, ..., APP-n]   (`a` here stands for `app`)
  as <- forM xts $ \(x, t) -> toAffineApp m x t
  ys <- mapM (const $ newNameWith' "arg") xts
  let body = bindLet (zip ys as) (m, CompUpIntro (m, ValueSigmaIntro []))
  body' <- linearize xts body
  return (m, CompSigmaElim (map fst xts) argVar body')

-- (Assuming `ti` = `return di` for some `di` such that `xi : di`)
-- relevantSigma NAME LOC [(x1, t1), ..., (xn, tn)]   ~>
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
relevantSigma ::
  Hint ->
  [Either CompPlus (Ident, CompPlus)] ->
  ValuePlus ->
  WithEnv CompPlus
relevantSigma m mxts argVar = do
  xts <- mapM supplyName mxts
  -- as == [APP-1, ..., APP-n]
  as <- forM xts $ \(x, t) -> toRelevantApp m x t
  -- pairVarNameList == [pair-1, ...,  pair-n]
  (pairVarNameList, pairVarTypeList) <- unzip <$> mapM toPairInfo xts
  transposedPair <- transposeSigma m pairVarTypeList
  let body = bindLet (zip pairVarNameList as) transposedPair
  body' <- linearize xts body
  return (m, CompSigmaElim (map fst xts) argVar body')

toPairInfo :: (Ident, CompPlus) -> WithEnv (Ident, (ValuePlus, CompPlus))
toPairInfo (_, t@(m, _)) = do
  (name, var) <- newValueUpsilonWith m "pair"
  return (name, (var, t))

-- transposeSigma [d1, ..., dn] :=
--   let (x1, y1) := d1 in
--   ...
--   let (xn, yn) := dn in
--   return ((x1, ..., xn), (y1, ..., yn))
transposeSigma :: Hint -> [(ValuePlus, CompPlus)] -> WithEnv CompPlus
transposeSigma m ds = do
  (xList, xVarList) <- unzip <$> mapM (const $ newValueUpsilonWith m "sig-x") ds
  (yList, yVarList) <- unzip <$> mapM (const $ newValueUpsilonWith m "sig-y") ds
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
      (fst cont, CompSigmaElim [x, y] d $ bindSigmaElim xyds cont)

supplyName :: Either b (Ident, b) -> WithEnv (Ident, b)
supplyName mName =
  case mName of
    Right (x, t) ->
      return (x, t)
    Left t -> do
      x <- newNameWith' "unused-sigarg"
      return (x, t)

cartClsName :: T.Text
cartClsName =
  "cartesian-closure"

returnClosureType :: Hint -> WithEnv CompPlus
returnClosureType m = do
  (env, envVar) <- newValueUpsilonWith m "env"
  retImmType <- returnCartesianImmediate m
  t <-
    cartesianSigma
      (Just cartClsName)
      m
      [Right (env, retImmType), Left (m, CompUpIntro envVar), Left retImmType]
  return (m, CompUpIntro t)
