module Clarify.Sigma
  ( cartesianSigma,
    returnArrayType,
    returnClosureType,
  )
where

import Clarify.Linearize
import Clarify.Utility
import Control.Monad.State.Lazy
import Data.Code
import Data.Env
import Data.Hint
import Data.Ident
import Data.LowType
import qualified Data.Text as T

cartesianSigma ::
  Maybe T.Text ->
  Hint ->
  ArrayKind ->
  [Either CodePlus (Ident, CodePlus)] ->
  WithEnv DataPlus
cartesianSigma mName m k mxts =
  case mName of
    Nothing -> do
      (args, e) <- makeSwitcher m (affineSigma m k mxts) (relevantSigma m k mxts)
      i <- newCount
      let h = "sigma-" <> T.pack (show i)
      insCodeEnv h False args e
      return (m, DataConst h)
    Just name ->
      tryCache m name $ do
        (args, e) <- makeSwitcher m (affineSigma m k mxts) (relevantSigma m k mxts)
        insCodeEnv name False args e

-- (Assuming `ti` = `return di` for some `di` such that `xi : di`)
-- affineSigma NAME LOC [(x1, t1), ..., (xn, tn)]   ~>
--   update CodeEnv with NAME ~> (thunk LAM), where LAM is:
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
  ArrayKind ->
  [Either CodePlus (Ident, CodePlus)] ->
  DataPlus ->
  WithEnv CodePlus
affineSigma m k mxts argVar = do
  xts <- mapM supplyName mxts
  -- as == [APP-1, ..., APP-n]   (`a` here stands for `app`)
  as <- forM xts $ \(x, t) -> toAffineApp m x t
  ys <- mapM (const $ newNameWith' "arg") xts
  let body = bindLet (zip ys as) (m, CodeUpIntro (m, sigmaIntro []))
  body' <- linearize xts body
  return (m, CodeSigmaElim k (map fst xts) argVar body')

-- (Assuming `ti` = `return di` for some `di` such that `xi : di`)
-- relevantSigma NAME LOC [(x1, t1), ..., (xn, tn)]   ~>
--   update CodeEnv with NAME ~> (thunk LAM), where LAM is:
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
  ArrayKind ->
  [Either CodePlus (Ident, CodePlus)] ->
  DataPlus ->
  WithEnv CodePlus
relevantSigma m k mxts argVar = do
  xts <- mapM supplyName mxts
  -- as == [APP-1, ..., APP-n]
  as <- forM xts $ \(x, t) -> toRelevantApp m x t
  -- pairVarNameList == [pair-1, ...,  pair-n]
  (pairVarNameList, pairVarTypeList) <- unzip <$> mapM toPairInfo xts
  transposedPair <- transposeSigma m k pairVarTypeList
  let body = bindLet (zip pairVarNameList as) transposedPair
  body' <- linearize xts body
  return (m, CodeSigmaElim k (map fst xts) argVar body')

toPairInfo :: (Ident, CodePlus) -> WithEnv (Ident, (DataPlus, CodePlus))
toPairInfo (_, t@(m, _)) = do
  (name, var) <- newDataUpsilonWith m "pair"
  return (name, (var, t))

-- transposeSigma [d1, ..., dn] :=
--   let (x1, y1) := d1 in
--   ...
--   let (xn, yn) := dn in
--   return ((x1, ..., xn), (y1, ..., yn))
transposeSigma :: Hint -> ArrayKind -> [(DataPlus, CodePlus)] -> WithEnv CodePlus
transposeSigma m k ds = do
  (xList, xVarList) <- unzip <$> mapM (const $ newDataUpsilonWith m "sig-x") ds
  (yList, yVarList) <- unzip <$> mapM (const $ newDataUpsilonWith m "sig-y") ds
  return $
    bindSigmaElim
      (zip (zip xList yList) ds)
      ( m,
        CodeUpIntro
          ( m,
            sigmaIntro
              [(m, DataSigmaIntro k xVarList), (m, DataSigmaIntro k yVarList)]
          )
      )

bindSigmaElim :: [((Ident, Ident), (DataPlus, CodePlus))] -> CodePlus -> CodePlus
bindSigmaElim binder cont =
  case binder of
    [] ->
      cont
    ((x, y), (d, _)) : xyds ->
      (fst cont, sigmaElim [x, y] d $ bindSigmaElim xyds cont)

supplyName :: Either b (Ident, b) -> WithEnv (Ident, b)
supplyName mName =
  case mName of
    Right (x, t) ->
      return (x, t)
    Left t -> do
      x <- newNameWith' "unused-sigarg"
      return (x, t)

cartArrayName :: T.Text
cartArrayName =
  "cartesian-array"

returnArrayType :: Hint -> WithEnv CodePlus
returnArrayType m = do
  (arr, arrVar) <- newDataUpsilonWith m "arr"
  retImmType <- returnCartesianImmediate m
  t <-
    cartesianSigma
      (Just cartArrayName)
      m
      arrVoidPtr
      [Right (arr, retImmType), Left (m, CodeUpIntro arrVar)]
  return (m, CodeUpIntro t)

cartClsName :: T.Text
cartClsName =
  "cartesian-closure"

returnClosureType :: Hint -> WithEnv CodePlus
returnClosureType m = do
  (env, envVar) <- newDataUpsilonWith m "env"
  retImmType <- returnCartesianImmediate m
  t <-
    cartesianSigma
      (Just cartClsName)
      m
      arrVoidPtr
      [Right (env, retImmType), Left (m, CodeUpIntro envVar), Left retImmType]
  return (m, CodeUpIntro t)
