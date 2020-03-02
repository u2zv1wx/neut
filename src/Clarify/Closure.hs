{-# LANGUAGE OverloadedStrings #-}

module Clarify.Closure
  ( makeClosure
  , callClosure
  , chainTermPlus
  , chainTermPlus'
  , chainTermPlus''
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.List

import qualified Data.HashMap.Strict as Map
import qualified Data.IntMap.Strict as IntMap

import Clarify.Linearize
import Clarify.Sigma
import Clarify.Utility
import Data.Basic
import Data.Code
import Data.Env
import Data.Term

makeClosure ::
     Maybe Identifier -- the name of newly created closure
  -> [(Meta, Identifier, CodePlus)] -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  -> Meta -- meta of lambda
  -> [(Meta, Identifier, CodePlus)] -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  -> CodePlus -- the `e` in `lam (x1, ..., xn). e`
  -> WithEnv DataPlus
makeClosure mName mxts2 m mxts1 e = do
  let (_, xs2, ts2) = unzip3 mxts2
  let xts2 = zip xs2 ts2
  let (_, xs1, ts1) = unzip3 mxts1
  let xts1 = zip xs1 ts1
  expName <- newNameWith' "exp"
  envExp <- cartesianSigma expName m arrVoidPtr $ map Right xts2
  (envVarName, envVar) <- newDataUpsilonWith "env"
  e' <- linearize (xts2 ++ xts1) e
  cenv <- gets codeEnv
  name <- nameFromMaybe mName
  let args = map fst xts1 ++ [envVarName]
  let body = (m, CodeSigmaElim arrVoidPtr xts2 envVar e')
  when (name `notElem` Map.keys cenv) $ insCodeEnv name args body
  let fvEnv = (m, DataSigmaIntro arrVoidPtr $ map (toDataUpsilon' . fst) xts2)
  return (m, DataSigmaIntro arrVoidPtr [envExp, fvEnv, (m, DataTheta name)])

callClosure ::
     Meta -> CodePlus -> [(Identifier, CodePlus, DataPlus)] -> WithEnv CodePlus
callClosure m e zexes = do
  let (zs, es', xs) = unzip3 zexes
  (clsVarName, clsVar) <- newDataUpsilonWith "closure"
  (typeVarName, _) <- newDataUpsilonWith "exp"
  (envVarName, envVar) <- newDataUpsilonWith "env"
  (lamVarName, lamVar) <- newDataUpsilonWith "thunk"
  retImmType <- returnCartesianImmediate
  return $
    bindLet
      ((clsVarName, e) : zip zs es')
      ( m
      , CodeSigmaElim
          arrVoidPtr
          [ (typeVarName, retImmType)
          , (envVarName, returnUpsilon typeVarName)
          , (lamVarName, retImmType)
          ]
          clsVar
          (m, CodePiElimDownElim lamVar (xs ++ [envVar])))

nameFromMaybe :: Maybe Identifier -> WithEnv Identifier
nameFromMaybe mName =
  case mName of
    Just lamThetaName -> return lamThetaName
    Nothing -> newNameWith' "thunk"

-- fixme : ここのtypeEnvは引数で取る必要があるはず。envだと壊れる。renameと同じ理由。
chainTermPlus :: TermPlus -> WithEnv [(Meta, Identifier, TermPlus)]
chainTermPlus e = do
  tmp <- chainTermPlus' e
  return $ nubBy (\(_, x, _) (_, y, _) -> x == y) tmp

chainTermPlus' :: TermPlus -> WithEnv [(Meta, Identifier, TermPlus)]
chainTermPlus' (_, TermTau _) = return []
chainTermPlus' (m, TermUpsilon x) = do
  t <- lookupTypeEnv' x
  xts <- chainWithName x t
  return $ xts ++ [(m, x, t)]
chainTermPlus' (_, TermPi _ xts t) = chainTermPlus'' xts [t]
chainTermPlus' (_, TermPiIntro xts e) = chainTermPlus'' xts [e]
chainTermPlus' (_, TermPiElim e es) = do
  xs1 <- chainTermPlus' e
  xs2 <- concat <$> mapM (chainTermPlus') es
  return $ xs1 ++ xs2
chainTermPlus' (_, TermSigma xts) = chainTermPlus'' xts []
chainTermPlus' (_, TermSigmaIntro t es) = do
  xs1 <- chainTermPlus' t
  xs2 <- concat <$> mapM chainTermPlus' es
  return $ xs1 ++ xs2
chainTermPlus' (_, TermSigmaElim t xts e1 e2) = do
  xs <- chainTermPlus' t
  ys <- chainTermPlus' e1
  zs <- chainTermPlus'' xts [e2]
  return $ xs ++ ys ++ zs
chainTermPlus' (_, TermIter (_, x, t) xts e) = do
  xs1 <- chainTermPlus' t
  insTypeEnv' x t
  xs2 <- chainTermPlus'' xts [e]
  return $ xs1 ++ filter (\(_, y, _) -> y /= x) xs2
chainTermPlus' (_, TermConst x) = do
  t <- lookupTypeEnv' x
  chainWithName x t
chainTermPlus' (_, TermConstDecl xt e) = chainTermPlus'' [xt] [e]
chainTermPlus' (_, TermFloat16 _) = return []
chainTermPlus' (_, TermFloat32 _) = return []
chainTermPlus' (_, TermFloat64 _) = return []
chainTermPlus' (_, TermEnum _) = return []
chainTermPlus' (_, TermEnumIntro _) = return []
chainTermPlus' (_, TermEnumElim (e, t) les) = do
  xs0 <- chainTermPlus' t
  xs1 <- chainTermPlus' e
  let es = map snd les
  xs2 <- concat <$> mapM (chainTermPlus') es
  return $ xs0 ++ xs1 ++ xs2
chainTermPlus' (_, TermArray dom _) = chainTermPlus' dom
chainTermPlus' (_, TermArrayIntro _ es) = do
  concat <$> mapM (chainTermPlus') es
chainTermPlus' (_, TermArrayElim _ xts e1 e2) = do
  xs1 <- chainTermPlus' e1
  xs2 <- chainTermPlus'' xts [e2]
  return $ xs1 ++ xs2
chainTermPlus' (_, TermStruct _) = return []
chainTermPlus' (_, TermStructIntro eks) =
  concat <$> mapM (chainTermPlus' . fst) eks
chainTermPlus' (_, TermStructElim xks e1 e2) = do
  xs1 <- chainTermPlus' e1
  xs2 <- chainTermPlus' e2
  let xs = map (\(_, y, _) -> y) xks
  return $ xs1 ++ filter (\(_, y, _) -> y `notElem` xs) xs2

chainTermPlus'' ::
     [(Meta, Identifier, TermPlus)]
  -> [TermPlus]
  -> WithEnv [(Meta, Identifier, TermPlus)]
chainTermPlus'' [] es = concat <$> mapM (chainTermPlus') es
chainTermPlus'' ((_, x, t):xts) es = do
  xs1 <- chainTermPlus' t
  insTypeEnv' x t
  xs2 <- chainTermPlus'' xts es
  return $ xs1 ++ filter (\(_, y, _) -> y /= x) xs2

-- assuming the type of `x` is `t`, obtain the closed chain of the type of `x`.
-- if the chain is computed for the first time, this function caches the computed result.
-- if not, use the cached result.
chainWithName ::
     Identifier -> TermPlus -> WithEnv [(Meta, Identifier, TermPlus)]
chainWithName (I (_, i)) t = do
  cenv <- gets chainEnv
  case IntMap.lookup i cenv of
    Just xts -> return xts -- use cached result
    Nothing -> do
      xts <- chainTermPlus' t
      modify (\env -> env {chainEnv = IntMap.insert i xts cenv})
      return xts
