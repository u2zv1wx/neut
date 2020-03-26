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

import qualified Data.Text as T

import Clarify.Linearize
import Clarify.Sigma
import Clarify.Utility
import Data.Basic
import Data.Code
import Data.Env
import Data.Term

makeClosure ::
     Maybe T.Text -- the name of newly created closure
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
  (envVarName, envVar) <- newDataUpsilonWith m "env"
  e' <- linearize (xts2 ++ xts1) e
  cenv <- gets codeEnv
  name <- nameFromMaybe mName
  let args = map fst xts1 ++ [envVarName]
  let body = (m, CodeSigmaElim arrVoidPtr (map fst xts2) envVar e')
  when (name `notElem` Map.keys cenv) $ insCodeEnv name args body
  let vs = map (\(mx, x, _) -> toDataUpsilon (x, mx)) mxts2
  let fvEnv = (m, DataSigmaIntro arrVoidPtr vs)
  return (m, DataSigmaIntro arrVoidPtr [envExp, fvEnv, (m, DataTheta name)])

callClosure ::
     Meta -> CodePlus -> [(Identifier, CodePlus, DataPlus)] -> WithEnv CodePlus
callClosure m e zexes = do
  let (zs, es', xs) = unzip3 zexes
  (clsVarName, clsVar) <- newDataUpsilonWith m "closure"
  (typeVarName, _) <- newDataUpsilonWith m "exp"
  (envVarName, envVar) <- newDataUpsilonWith m "env"
  (lamVarName, lamVar) <- newDataUpsilonWith m "thunk"
  return $
    bindLet
      ((clsVarName, e) : zip zs es')
      ( m
      , CodeSigmaElim
          arrVoidPtr
          [typeVarName, envVarName, lamVarName]
          clsVar
          (m, CodePiElimDownElim lamVar (xs ++ [envVar])))

nameFromMaybe :: Maybe T.Text -> WithEnv T.Text
nameFromMaybe mName =
  case mName of
    Just lamThetaName -> return lamThetaName
    Nothing -> asText' <$> newNameWith' "thunk"

chainTermPlus :: TermPlus -> WithEnv [IdentifierPlus]
chainTermPlus e = do
  tenv <- gets typeEnv
  tmp <- chainTermPlus' tenv e
  return $ nubBy (\(_, x, _) (_, y, _) -> x == y) tmp

chainTermPlus' :: TypeEnv -> TermPlus -> WithEnv [IdentifierPlus]
chainTermPlus' _ (_, TermTau _) = return []
chainTermPlus' tenv (m, TermUpsilon x) = do
  t <- lookupTypeEnv'' m x tenv
  xts <- chainTermPlus' tenv t
  return $ xts ++ [(m, x, t)]
chainTermPlus' tenv (_, TermPi _ xts t) = chainTermPlus'' tenv xts [t]
chainTermPlus' tenv (_, TermPiPlus _ _ xts t) = chainTermPlus'' tenv xts [t]
chainTermPlus' tenv (_, TermPiIntro xts e) = chainTermPlus'' tenv xts [e]
chainTermPlus' tenv (_, TermPiIntroNoReduce xts e) =
  chainTermPlus'' tenv xts [e]
chainTermPlus' tenv (_, TermPiIntroPlus _ _ xts e) =
  chainTermPlus'' tenv xts [e]
chainTermPlus' tenv (_, TermPiElim e es) = do
  xs1 <- chainTermPlus' tenv e
  xs2 <- concat <$> mapM (chainTermPlus' tenv) es
  return $ xs1 ++ xs2
chainTermPlus' tenv (_, TermSigma xts) = chainTermPlus'' tenv xts []
chainTermPlus' tenv (_, TermSigmaIntro t es) = do
  xs1 <- chainTermPlus' tenv t
  xs2 <- concat <$> mapM (chainTermPlus' tenv) es
  return $ xs1 ++ xs2
chainTermPlus' tenv (_, TermSigmaElim t xts e1 e2) = do
  xs <- chainTermPlus' tenv t
  ys <- chainTermPlus' tenv e1
  zs <- chainTermPlus'' tenv xts [e2]
  return $ xs ++ ys ++ zs
chainTermPlus' tenv (_, TermIter (_, x, t) xts e) = do
  xs1 <- chainTermPlus' tenv t
  xs2 <- chainTermPlus'' (insTypeEnv'' x t tenv) xts [e]
  return $ xs1 ++ filter (\(_, y, _) -> y /= x) xs2
chainTermPlus' tenv (m, TermConst x) = do
  t <- lookupTypeEnv'' m x tenv
  chainTermPlus' tenv t
chainTermPlus' _ (_, TermFloat16 _) = return []
chainTermPlus' _ (_, TermFloat32 _) = return []
chainTermPlus' _ (_, TermFloat64 _) = return []
chainTermPlus' _ (_, TermEnum _) = return []
chainTermPlus' _ (_, TermEnumIntro _) = return []
chainTermPlus' tenv (_, TermEnumElim (e, t) les) = do
  xs0 <- chainTermPlus' tenv t
  xs1 <- chainTermPlus' tenv e
  let es = map snd les
  xs2 <- concat <$> mapM (chainTermPlus' tenv) es
  return $ xs0 ++ xs1 ++ xs2
chainTermPlus' tenv (_, TermArray dom _) = chainTermPlus' tenv dom
chainTermPlus' tenv (_, TermArrayIntro _ es) = do
  concat <$> mapM (chainTermPlus' tenv) es
chainTermPlus' tenv (_, TermArrayElim _ xts e1 e2) = do
  xs1 <- chainTermPlus' tenv e1
  xs2 <- chainTermPlus'' tenv xts [e2]
  return $ xs1 ++ xs2
chainTermPlus' _ (_, TermStruct _) = return []
chainTermPlus' tenv (_, TermStructIntro eks) =
  concat <$> mapM (chainTermPlus' tenv . fst) eks
chainTermPlus' tenv (_, TermStructElim xks e1 e2) = do
  xs1 <- chainTermPlus' tenv e1
  xs2 <- chainTermPlus' tenv e2
  let xs = map (\(_, y, _) -> y) xks
  return $ xs1 ++ filter (\(_, y, _) -> y `notElem` xs) xs2
chainTermPlus' tenv (_, TermCase (e, t) cxtes) = do
  xs <- chainTermPlus' tenv e
  ys <- chainTermPlus' tenv t
  zs <-
    concat <$> mapM (\((_, xts), body) -> chainTermPlus'' tenv xts [body]) cxtes
  return $ xs ++ ys ++ zs

chainTermPlus'' ::
     TypeEnv -> [IdentifierPlus] -> [TermPlus] -> WithEnv [IdentifierPlus]
chainTermPlus'' tenv [] es = concat <$> mapM (chainTermPlus' tenv) es
chainTermPlus'' tenv ((_, x, t):xts) es = do
  xs1 <- chainTermPlus' tenv t
  xs2 <- chainTermPlus'' (insTypeEnv'' x t tenv) xts es
  return $ xs1 ++ filter (\(_, y, _) -> y /= x) xs2
