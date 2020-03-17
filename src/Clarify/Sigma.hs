{-# LANGUAGE OverloadedStrings #-}

module Clarify.Sigma
  ( cartesianSigma
  , returnArrayType
  , returnClosureType
  ) where

import Control.Monad.Except
import Control.Monad.State

import qualified Data.HashMap.Strict as Map

import Clarify.Linearize
import Clarify.Utility
import Data.Basic
import Data.Code
import Data.Env

cartesianSigma ::
     Identifier
  -> Meta
  -> ArrayKind
  -> [Either CodePlus (Identifier, CodePlus)]
  -> WithEnv DataPlus
cartesianSigma (I (thetaName, i)) m k mxts = do
  cenv <- gets codeEnv
  let ident = asText' $ I ("cartesian-" <> thetaName, i)
  let theta = (m, DataTheta ident)
  case Map.lookup ident cenv of
    Just _ -> return theta
    Nothing -> do
      (switchVarName, switchVar) <- newDataUpsilonWith "switch"
      (argVarName, argVar) <- newDataUpsilonWith "argsig"
      aff <- affineSigma argVar m k mxts
      rel <- relevantSigma argVar m k mxts
      insCodeEnv
        ident
        [switchVarName, argVarName]
        ( emptyMeta
        , CodeEnumElim
            [(argVarName, argVar)]
            switchVar
            -- [(CaseValue (EnumValueIntS 64 0), aff), (CaseDefault, rel)])
            [(LowCaseValueIntS 64 0, aff), (LowCaseDefault, rel)])
      return theta

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
     DataPlus
  -> Meta
  -> ArrayKind
  -> [Either CodePlus (Identifier, CodePlus)]
  -> WithEnv CodePlus
affineSigma argVar m k mxts = do
  xts <- mapM supplyName mxts
  -- as == [APP-1, ..., APP-n]   (`a` here stands for `app`)
  as <- forM xts $ \(x, t) -> toAffineApp m x t
  ys <- mapM (const $ newNameWith' "arg") xts
  let body =
        bindLet (zip ys as) (m, CodeUpIntro (m, DataSigmaIntro arrVoidPtr []))
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
     DataPlus
  -> Meta
  -> ArrayKind
  -> [Either CodePlus (Identifier, CodePlus)]
  -> WithEnv CodePlus
relevantSigma argVar m k mxts = do
  xts <- mapM supplyName mxts
  -- as == [APP-1, ..., APP-n]
  as <- forM xts $ \(x, t) -> toRelevantApp m x t
  -- pairVarNameList == [pair-1, ...,  pair-n]
  (pairVarNameList, pairVarTypeList) <- unzip <$> mapM toPairInfo xts
  transposedPair <- transposeSigma k pairVarTypeList
  let body = bindLet (zip pairVarNameList as) transposedPair
  body' <- linearize xts body
  return (m, CodeSigmaElim k (map fst xts) argVar body')

toPairInfo ::
     (Identifier, CodePlus) -> WithEnv (Identifier, (DataPlus, CodePlus))
toPairInfo (_, t) = do
  (name, var) <- newDataUpsilonWith "pair"
  return (name, (var, t))

-- transposeSigma [d1, ..., dn] :=
--   let (x1, y1) := d1 in
--   ...
--   let (xn, yn) := dn in
--   return ((x1, ..., xn), (y1, ..., yn))
transposeSigma :: ArrayKind -> [(DataPlus, CodePlus)] -> WithEnv CodePlus
transposeSigma k ds = do
  (xVarNameList, xVarList) <-
    unzip <$> mapM (const $ newDataUpsilonWith "sig-x") ds
  (yVarNameList, yVarList) <-
    unzip <$> mapM (const $ newDataUpsilonWith "sig-y") ds
  return $
    bindSigmaElim (zip (zip xVarNameList yVarNameList) ds) $
    ( emptyMeta
    , CodeUpIntro
        ( emptyMeta
        , DataSigmaIntro
            arrVoidPtr
            [ (emptyMeta, DataSigmaIntro k xVarList)
            , (emptyMeta, DataSigmaIntro k yVarList)
            ]))

bindSigmaElim ::
     [((Identifier, Identifier), (DataPlus, CodePlus))] -> CodePlus -> CodePlus
bindSigmaElim [] cont = cont
bindSigmaElim (((x, y), (d, _)):xyds) cont = do
  let cont' = bindSigmaElim xyds cont
  (fst cont', CodeSigmaElim arrVoidPtr [x, y] d cont')

supplyName :: Either b (Identifier, b) -> WithEnv (Identifier, b)
supplyName (Right (x, t)) = return (x, t)
supplyName (Left t) = do
  x <- newNameWith' "unused-sigarg"
  return (x, t)

returnArrayType :: Meta -> WithEnv CodePlus
returnArrayType ml = do
  (arrVarName, arrVar) <- newDataUpsilonWith "arr"
  retImmType <- returnCartesianImmediate
  let retArrVar = (ml, CodeUpIntro arrVar)
  v <-
    cartesianSigma
      (I ("array-closure", 0))
      ml
      arrVoidPtr
      [Right (arrVarName, retImmType), Left retArrVar]
  return (ml, CodeUpIntro v)

returnClosureType :: Meta -> WithEnv CodePlus
returnClosureType m = do
  (envVarName, envVar) <- newDataUpsilonWith "env"
  retImmType <- returnCartesianImmediate
  let retEnvVar = (m, CodeUpIntro envVar)
  closureType <-
    cartesianSigma
      (I ("closure", 0))
      m
      arrVoidPtr
      [Right (envVarName, retImmType), Left retEnvVar, Left retImmType]
  return (m, CodeUpIntro closureType)
