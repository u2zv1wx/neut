module Clarify.Closure
  ( makeClosure
  , callClosure
  , varTermPlus
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.List
import Prelude hiding (pi)

import Clarify.Linearize
import Clarify.Sigma
import Clarify.Utility
import Data.Basic
import Data.Code
import Data.Env
import Data.Term

makeClosure ::
     Maybe Identifier -- the name of newly created closure
  -> [(Identifier, Meta, CodePlus)] -- list of free variables in `lam (x1, ..., xn). e` (this must be a closed chain)
  -> Meta -- meta of lambda
  -> [(Identifier, CodePlus)] -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  -> CodePlus -- the `e` in `lam (x1, ..., xn). e`
  -> WithEnv CodePlus
makeClosure mName fvs m xts e = do
  let (freeVarNameList, locList, negTypeList) = unzip3 fvs
  expName <- newNameWith "exp"
  envExp <-
    cartesianSigma expName m $ map Right $ zip freeVarNameList negTypeList
  (envVarName, envVar) <- newDataUpsilonWith "env"
  let fvInfo = zip freeVarNameList negTypeList
  -- envVarがlinearなのは既知
  -- body <- linearize (zip xs ts') $ (m, CodeSigmaElim fvInfo envVar e)
  body <- linearize xts $ (m, CodeSigmaElim fvInfo envVar e)
  let fvSigmaIntro =
        ( m
        , DataSigmaIntro $ zipWith (curry toDataUpsilon) freeVarNameList locList)
  name <-
    case mName of
      Just lamThetaName -> return lamThetaName
      Nothing -> newNameWith "thunk"
  cenv <- gets codeEnv
  when (name `notElem` map fst cenv) $
    insCodeEnv name (envVarName : map fst xts) body
  return $
    ( m
    , CodeUpIntro
        (m, DataSigmaIntro [envExp, fvSigmaIntro, (m, DataTheta name)]))

--  when (name == "thunk-413") $ do
callClosure ::
     Meta -> CodePlus -> [(Identifier, CodePlus, DataPlus)] -> WithEnv CodePlus
callClosure m e zexes = do
  let (zs, es', xs) = unzip3 zexes
  -- (zs, es', xs) <- unzip3 <$> mapM clarify' es
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

varTermPlus :: TermPlus -> WithEnv [(Identifier, Meta, TermPlus)]
varTermPlus e = do
  tmp <- getClosedVarChain e
  return $ nubBy (\(x, _, _) (y, _, _) -> x == y) tmp

getClosedVarChain :: TermPlus -> WithEnv [(Identifier, Meta, TermPlus)]
getClosedVarChain (_, TermTau) = return []
getClosedVarChain (_, TermTheta _) = return []
getClosedVarChain (m, TermUpsilon x) = do
  t <- lookupTypeEnv x
  xs <- getClosedVarChain t
  return $ xs ++ [(x, m, t)]
getClosedVarChain (_, TermPi xts t) = getClosedVarChainBindings xts [t]
getClosedVarChain (_, TermPiIntro xts e) = getClosedVarChainBindings xts [e]
getClosedVarChain (_, TermPiElim e es) = do
  xs1 <- getClosedVarChain e
  xs2 <- concat <$> mapM getClosedVarChain es
  return $ xs1 ++ xs2
getClosedVarChain (_, TermMu ut e) = getClosedVarChainBindings [ut] [e]
getClosedVarChain (_, TermIntS _ _) = return []
getClosedVarChain (_, TermIntU _ _) = return []
getClosedVarChain (_, TermFloat16 _) = return []
getClosedVarChain (_, TermFloat32 _) = return []
getClosedVarChain (_, TermFloat64 _) = return []
getClosedVarChain (_, TermEnum _) = return []
getClosedVarChain (_, TermEnumIntro _) = return []
getClosedVarChain (_, TermEnumElim e les) = do
  xs1 <- getClosedVarChain e
  let es = map snd les
  xs2 <- concat <$> mapM getClosedVarChain es
  return $ xs1 ++ xs2
getClosedVarChain (_, TermArray _ indexType) = getClosedVarChain indexType
getClosedVarChain (_, TermArrayIntro _ les) = do
  let es = map snd les
  concat <$> mapM getClosedVarChain es
getClosedVarChain (_, TermArrayElim _ e1 e2) = do
  xs1 <- getClosedVarChain e1
  xs2 <- getClosedVarChain e2
  return $ xs1 ++ xs2

getClosedVarChainBindings ::
     [(Identifier, TermPlus)]
  -> [TermPlus]
  -> WithEnv [(Identifier, Meta, TermPlus)]
getClosedVarChainBindings [] es = concat <$> mapM getClosedVarChain es
getClosedVarChainBindings ((x, t):xts) es = do
  xs1 <- getClosedVarChain t
  xs2 <- getClosedVarChainBindings xts es
  return $ xs1 ++ filter (\(y, _, _) -> y /= x) xs2
