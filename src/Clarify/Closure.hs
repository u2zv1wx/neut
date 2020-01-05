module Clarify.Closure
  ( makeClosure
  , callClosure
  , varTermPlus
  , varTermPlus''
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

import qualified Data.Map.Strict as Map

makeClosure ::
     Maybe Identifier -- the name of newly created closure
  -> [(Identifier, CodePlus)] -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  -> Meta -- meta of lambda
  -> [(Identifier, CodePlus)] -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  -> CodePlus -- the `e` in `lam (x1, ..., xn). e`
  -> WithEnv CodePlus
makeClosure mName xts2 m xts1 e = do
  expName <- newNameWith "exp"
  envExp <- cartesianSigma expName m $ map Right xts2
  (envVarName, envVar) <- newDataUpsilonWith "env"
  e' <- linearize (xts2 ++ xts1) e
  cenv <- gets codeEnv
  name <- nameFromMaybe mName
  let args = envVarName : map fst xts1
  let body = (m, CodeSigmaElim xts2 envVar e')
  when (name `notElem` map fst cenv) $ insCodeEnv name args body
  let fvEnv = (m, DataSigmaIntro $ map (toDataUpsilon' . fst) xts2)
  let cls = (m, DataSigmaIntro [envExp, fvEnv, (m, DataTheta name)])
  return (m, CodeUpIntro cls)

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
          [ (typeVarName, retUnivType)
          , (envVarName, returnUpsilon typeVarName)
          , (lamVarName, retImmType)
          ]
          clsVar
          ( m
          , CodeSigmaElim
              [(affVarName, retImmType), (relVarName, retImmType)]
              typeVar
              (m, CodePiElimDownElim lamVar (envVar : xs))))

nameFromMaybe :: Maybe Identifier -> WithEnv Identifier
nameFromMaybe mName =
  case mName of
    Just lamThetaName -> return lamThetaName
    Nothing -> newNameWith "thunk"

varTermPlus :: TermPlus -> WithEnv [(Identifier, TermPlus)]
varTermPlus e = do
  tmp <- varTermPlus' e
  return $ nubBy (\(x, _) (y, _) -> x == y) tmp

varTermPlus' :: TermPlus -> WithEnv [(Identifier, TermPlus)]
varTermPlus' (_, TermTau) = return []
varTermPlus' (_, TermUpsilon x)
  -- enum.n{i} : is-enum n{i}. since `is-enum` is a constant, the type of enum.n{i} doesn't have any variables.
  | Just _ <- asEnumNatNumConstant x = return []
  -- i64, f32, u1234 : univ
  | Just _ <- asLowTypeMaybe x = return []
  -- constant or ordinary variable
  | otherwise = do
    t <- lookupTypeEnv x
    xts <- chainWithName x t
    cenv <- gets constantEnv
    if x `elem` cenv
      then return xts
      else return $ xts ++ [(x, t)]
varTermPlus' (_, TermPi xts t) = varTermPlus'' xts [t]
varTermPlus' (_, TermPiIntro xts e) = varTermPlus'' xts [e]
varTermPlus' (_, TermPiElim e es) = do
  xs1 <- varTermPlus' e
  xs2 <- concat <$> mapM (varTermPlus') es
  return $ xs1 ++ xs2
varTermPlus' (_, TermMu xt e) = varTermPlus'' [xt] [e]
varTermPlus' (_, TermTheta xt e) = varTermPlus'' [xt] [e]
varTermPlus' (_, TermIntS _ _) = return []
varTermPlus' (_, TermIntU _ _) = return []
varTermPlus' (_, TermFloat16 _) = return []
varTermPlus' (_, TermFloat32 _) = return []
varTermPlus' (_, TermFloat64 _) = return []
varTermPlus' (_, TermEnum _) = return []
varTermPlus' (_, TermEnumIntro _) = return []
varTermPlus' (_, TermEnumElim e les) = do
  xs1 <- varTermPlus' e
  let es = map snd les
  xs2 <- concat <$> mapM (varTermPlus') es
  return $ xs1 ++ xs2
varTermPlus' (_, TermArray _ indexType) = varTermPlus' indexType
varTermPlus' (_, TermArrayIntro _ les) = do
  let es = map snd les
  concat <$> mapM (varTermPlus') es
varTermPlus' (_, TermArrayElim _ e1 e2) = do
  xs1 <- varTermPlus' e1
  xs2 <- varTermPlus' e2
  return $ xs1 ++ xs2

varTermPlus'' ::
     [(Identifier, TermPlus)] -> [TermPlus] -> WithEnv [(Identifier, TermPlus)]
varTermPlus'' [] es = concat <$> mapM (varTermPlus') es
varTermPlus'' ((x, t):xts) es = do
  xs1 <- varTermPlus' t
  xs2 <- varTermPlus'' xts es
  return $ xs1 ++ filter (\(y, _) -> y /= x) xs2

-- assuming the type of `x` is `t`, obtain the closed chain of the type of `x`.
-- if the chain is computed for the first time, this function caches the computed result.
-- if not, use the cached result.
chainWithName :: Identifier -> TermPlus -> WithEnv [(Identifier, TermPlus)]
chainWithName x t = do
  cenv <- gets chainEnv
  case Map.lookup x cenv of
    Just xts -> return xts -- use cached result
    Nothing -> do
      xts <- varTermPlus' t
      modify (\env -> env {chainEnv = Map.insert x xts cenv})
      return xts
