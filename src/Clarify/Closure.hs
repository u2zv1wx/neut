module Clarify.Closure
  ( makeClosure
  , callClosure
  , varTermPlus
  , getClosedChainBindings
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
  -- when
  --   (name `elem`
  --    [ "thunk-74450"
  --    , "thunk-73997"
  --    , "thunk-71507"
  --    , "thunk-70675"
  --    , "thunk-68875"
  --    , "thunk-66147"
  --    , "thunk-63567"
  --    , "thunk-59793"
  --    , "thunk-55814"
  --    , "thunk-49906"
  --    , "thunk-45765"
  --    ]) $ do
  --   p name
  --   p "args:"
  --   p' args
  --   p "fvs:"
  --   p' xts2
  --   p "body-orig:"
  --   p' e
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

varTermPlus :: Context -> TermPlus -> WithEnv [(Identifier, TermPlus)]
varTermPlus ctx e = do
  tmp <- getClosedChain ctx e
  return $ nubBy (\(x, _) (y, _) -> x == y) tmp

getClosedChain :: Context -> TermPlus -> WithEnv [(Identifier, TermPlus)]
getClosedChain _ (_, TermTau) = return []
getClosedChain ctx (_, TermTheta z) = do
  cenv <- gets chainEnv
  -- t <- lookupTypeEnv z
  t <- lookupContext z ctx
  case Map.lookup z cenv of
    Just xts -> return xts
    Nothing -> do
      xts <- getClosedChain ctx t
      modify (\env -> env {chainEnv = Map.insert z xts cenv})
      return xts
getClosedChain ctx (_, TermUpsilon x) = do
  cenv <- gets chainEnv
  t <- lookupContext x ctx
  -- t <- lookupTypeEnv x
  case Map.lookup x cenv of
    Just xts -> return $ xts ++ [(x, t)]
    Nothing -> do
      xts <- getClosedChain ctx t
      modify (\env -> env {chainEnv = Map.insert x xts cenv})
      return $ xts ++ [(x, t)]
getClosedChain ctx (_, TermPi xts t) = getClosedChainBindings ctx xts [t]
getClosedChain ctx (_, TermPiIntro xts e) = getClosedChainBindings ctx xts [e]
getClosedChain ctx (_, TermPiElim e es) = do
  xs1 <- getClosedChain ctx e
  xs2 <- concat <$> mapM (getClosedChain ctx) es
  return $ xs1 ++ xs2
getClosedChain ctx (_, TermMu ut e) = getClosedChainBindings ctx [ut] [e]
getClosedChain _ (_, TermIntS _ _) = return []
getClosedChain _ (_, TermIntU _ _) = return []
getClosedChain _ (_, TermFloat16 _) = return []
getClosedChain _ (_, TermFloat32 _) = return []
getClosedChain _ (_, TermFloat64 _) = return []
getClosedChain _ (_, TermEnum _) = return []
getClosedChain _ (_, TermEnumIntro _) = return []
getClosedChain ctx (_, TermEnumElim e les) = do
  xs1 <- getClosedChain ctx e
  let es = map snd les
  xs2 <- concat <$> mapM (getClosedChain ctx) es
  return $ xs1 ++ xs2
getClosedChain ctx (_, TermArray _ indexType) = getClosedChain ctx indexType
getClosedChain ctx (_, TermArrayIntro _ les) = do
  let es = map snd les
  concat <$> mapM (getClosedChain ctx) es
getClosedChain ctx (_, TermArrayElim _ e1 e2) = do
  xs1 <- getClosedChain ctx e1
  xs2 <- getClosedChain ctx e2
  return $ xs1 ++ xs2

getClosedChainBindings ::
     Context
  -> [(Identifier, TermPlus)]
  -> [TermPlus]
  -> WithEnv [(Identifier, TermPlus)]
getClosedChainBindings ctx [] es = concat <$> mapM (getClosedChain ctx) es
getClosedChainBindings ctx ((x, t):xts) es = do
  xs1 <- getClosedChain ctx t
  xs2 <- getClosedChainBindings ((x, t) : ctx) xts es
  return $ xs1 ++ filter (\(y, _) -> y /= x) xs2
