{-# LANGUAGE OverloadedStrings #-}

module Clarify.Closure
  ( makeClosure
  , callClosure
  , chainTermPlus
  , chainTermPlus''
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.List

import Clarify.Linearize
import Clarify.Sigma
import Clarify.Utility
import Data.Basic
import Data.Code
import Data.Env
import Data.Term

import qualified Data.HashMap.Strict as Map

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
  expName <- newNameWith "exp"
  envExp <- cartesianSigma expName m arrVoidPtr $ map Right xts2
  (envVarName, envVar) <- newDataUpsilonWith "env"
  let xts = xts2 ++ xts1
  let info1 = toInfo "makeClosure: arg of linearize is not closed chain:" xts
  assertUP info1 $ isClosedChain xts
  -- これxts1がclosedとは限らないんでは？
  -- いや、closedchainを構成するときにけっきょくxts2に入ってくるから問題ないのか。
  e' <- linearize (xts2 ++ xts1) e
  cenv <- gets codeEnv
  name <- nameFromMaybe mName
  let args = envVarName : map fst xts1
  let body = (m, CodeSigmaElim arrVoidPtr xts2 envVar e')
  when (name `notElem` Map.keys cenv) $ insCodeEnv name args body
  let fvEnv = (m, DataSigmaIntro arrVoidPtr $ map (toDataUpsilon' . fst) xts2)
  return (m, DataSigmaIntro arrVoidPtr [envExp, fvEnv, (m, DataTheta name)])
  -- let cls = (m, DataSigmaIntro [envExp, fvEnv, (m, DataTheta name)])
  -- return (m, CodeUpIntro cls)

callClosure ::
     Meta -> CodePlus -> [(Identifier, CodePlus, DataPlus)] -> WithEnv CodePlus
callClosure m e zexes = do
  let (zs, es', xs) = unzip3 zexes
  (clsVarName, clsVar) <- newDataUpsilonWith "closure"
  (typeVarName, typeVar) <- newDataUpsilonWith "exp"
  (envVarName, envVar) <- newDataUpsilonWith "env"
  (lamVarName, lamVar) <- newDataUpsilonWith "thunk"
  affVarName <- newNameWith "aff"
  relVarName <- newNameWith "rel"
  retUnivType <- returnCartesianUniv
  retImmType <- returnCartesianImmediate
  return $
    bindLet
      ((clsVarName, e) : zip zs es')
      ( m
      , CodeSigmaElim
          arrVoidPtr
          [ (typeVarName, retUnivType)
          , (envVarName, returnUpsilon typeVarName)
          , (lamVarName, retImmType)
          ]
          clsVar
          ( m
          , CodeSigmaElim
              arrVoidPtr
              [(affVarName, retImmType), (relVarName, retImmType)]
              typeVar
              (m, CodePiElimDownElim lamVar (envVar : xs))))

nameFromMaybe :: Maybe Identifier -> WithEnv Identifier
nameFromMaybe mName =
  case mName of
    Just lamThetaName -> return lamThetaName
    Nothing -> newNameWith "thunk"

chainTermPlus :: TermPlus -> WithEnv [(Meta, Identifier, TermPlus)]
chainTermPlus e = do
  tmp <- chainTermPlus' e
  return $ nubBy (\(_, x, _) (_, y, _) -> x == y) tmp

chainTermPlus' :: TermPlus -> WithEnv [(Meta, Identifier, TermPlus)]
chainTermPlus' (_, TermTau) = return []
chainTermPlus' (m, TermUpsilon x) = do
  t <- lookupTypeEnv x
  xts <- chainWithName x t
  return $ xts ++ [(m, x, t)]
chainTermPlus' (_, TermPi xts t) = chainTermPlus'' xts [t]
chainTermPlus' (_, TermPiIntro xts e) = chainTermPlus'' xts [e]
chainTermPlus' (_, TermPiElim e es) = do
  xs1 <- chainTermPlus' e
  xs2 <- concat <$> mapM (chainTermPlus') es
  return $ xs1 ++ xs2
chainTermPlus' (_, TermIter (_, x, t) xts e) = do
  xs1 <- chainTermPlus' t
  xs2 <- chainTermPlus'' xts [e]
  return $ xs1 ++ filter (\(_, y, _) -> y /= x) xs2
chainTermPlus' (_, TermConst x) = do
  t <- lookupTypeEnv x
  chainWithName x t
chainTermPlus' (_, TermConstDecl xt e) = chainTermPlus'' [xt] [e]
chainTermPlus' (_, TermFloat16 _) = return []
chainTermPlus' (_, TermFloat32 _) = return []
chainTermPlus' (_, TermFloat64 _) = return []
chainTermPlus' (_, TermEnum _) = return []
chainTermPlus' (_, TermEnumIntro _) = return []
chainTermPlus' (_, TermEnumElim e les) = do
  xs1 <- chainTermPlus' e
  let es = map snd les
  xs2 <- concat <$> mapM (chainTermPlus') es
  return $ xs1 ++ xs2
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
  insTypeEnv x t
  xs2 <- chainTermPlus'' xts es
  return $ xs1 ++ filter (\(_, y, _) -> y /= x) xs2

-- assuming the type of `x` is `t`, obtain the closed chain of the type of `x`.
-- if the chain is computed for the first time, this function caches the computed result.
-- if not, use the cached result.
chainWithName ::
     Identifier -> TermPlus -> WithEnv [(Meta, Identifier, TermPlus)]
chainWithName x t = do
  cenv <- gets chainEnv
  case Map.lookup x cenv of
    Just xts -> return xts -- use cached result
    Nothing -> do
      xts <- chainTermPlus' t
      modify (\env -> env {chainEnv = Map.insert x xts cenv})
      return xts
