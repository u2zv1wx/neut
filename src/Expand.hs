-- Every type is converted into an "exponent", which is a function that receives
-- an integer `n` and a term `e` of that type, and returns n-copy of `e`, namely,
-- returns (e, ..., e). This operation roughly corresponds to eta-expansion. Indeed,
-- when the integer `n` equals to 1, this exponential operation degenerates to
-- eta-expansion.
module Expand
  ( expand
  ) where

import           Control.Monad.Except
import           Control.Monad.State
import           Prelude              hiding (pi)
import           Text.Read            (readMaybe)

import           Data.Basic
import           Data.Code
import           Data.Env
import           Data.LowCode
import           Reduce.Code

expand :: CodePlus -> WithEnv LowCodePlus
expand mainTerm = do
  cenv <- gets codeEnv
  forM_ cenv $ \(lamThetaName, (args, body)) -> do
    body' <- inlineCodePlus body
    if isEtaExpandableCode body'
      then expandCode body' >>= insLowCodeEnv lamThetaName args
      else throwError "expand"
  mainTerm' <- inlineCodePlus mainTerm
  if isEtaExpandableCode mainTerm'
    then expandCode mainTerm'
    else throwError "expand"

expandData :: DataPlus -> WithEnv LowDataPlus
expandData (_, DataTau) = exponentImmediate
expandData (m, DataTheta theta) = return (m, LowDataTheta theta)
expandData (m, DataUpsilon x) = return (m, LowDataUpsilon x)
expandData (_, DataEpsilon _) = exponentImmediate
expandData (m, DataEpsilonIntro l t) = do
  lowType <- asLowType t
  return (m, LowDataEpsilonIntro l lowType)
expandData (_, DataDownPi _) = exponentImmediate
expandData (m, DataDownIntroPiIntro xs e) = do
  lamThetaName <- newNameWith "theta"
  e' <- expandCode e
  insLowCodeEnv lamThetaName xs e'
  return (m, LowDataTheta lamThetaName)
expandData (_, DataSigma xps) = do
  let (xs, ps) = unzip xps
  ps' <- mapM expandData ps
  exponentSigma "foo" Nothing (map Right (zip xs ps'))
expandData (m, DataSigmaIntro vs) = do
  vs' <- mapM expandData vs
  return (m, LowDataSigmaIntro vs')

expandCode :: CodePlus -> WithEnv LowCodePlus
expandCode (m, CodeTheta theta) = do
  theta' <- expandTheta theta
  return (m, LowCodeTheta theta')
expandCode (m, CodeEpsilonElim x v branchList) = do
  let (cs, es) = unzip branchList
  v' <- expandData v
  es' <- mapM expandCode es
  return (m, LowCodeEpsilonElim x v' (zip cs es'))
expandCode (m, CodePiElimDownElim v es) = do
  v' <- expandData v
  es' <- mapM expandCode es
  return (m, LowCodePiElimDownElim v' es')
expandCode (m, CodeSigmaElim xs v e) = do
  v' <- expandData v
  e' <- expandCode e
  return (m, LowCodeSigmaElim xs v' e')
expandCode (m, CodeUp v) = do
  v' <- expandData v
  return (m, LowCodeUpIntro v')
expandCode (m, CodeUpIntro v) = do
  v' <- expandData v
  return (m, LowCodeUpIntro v')

expandTheta :: Theta -> WithEnv LowDataTheta
expandTheta (ThetaArith op t v1 v2) = do
  lowType <- asLowType t
  v1' <- expandData v1
  v2' <- expandData v2
  return $ LowDataThetaArith op lowType v1' v2'
expandTheta (ThetaPrint v) = do
  v' <- expandData v
  return $ LowDataThetaPrint v'

exponentImmediate :: WithEnv LowDataPlus
exponentImmediate = do
  penv <- gets codeEnv
  let thetaName = "EXPONENT.IMMEDIATE"
  let immExp = (Nothing, LowDataTheta thetaName)
  case lookup thetaName penv of
    Just _ -> return immExp
    Nothing -> do
      (countVarName, countVar) <- newLowDataUpsilon
      (immVarName, immVar) <- newLowDataUpsilon
      let lamBody = (Nothing, LowCodeCopyN countVar immVar)
      insLowCodeEnv thetaName [countVarName, immVarName] lamBody
      return (Nothing, LowDataTheta thetaName)

-- Sigma (y1 : t1, ..., yn : tn) ~>
--   lam (m, z).
--     let (y1, ..., yn) := z in
--     bind ys1 = t1 @ (m, y1) in
--     ...
--     bind ysn = tn @ (m, yn) in
--     let (ys1-1, ..., ys1-m) := ys1 in
--     ...
--     let (ysn-1, ..., ysn-m) := ysn in
--     ((ys1-1, ..., ysn-1), ..., (ys1-m, ..., ysn-m))
--
-- (Note that Sigma (y1 : t1, ..., yn : tn) must be closed.)
exponentSigma ::
     Identifier
  -> Maybe Loc
  -> [Either LowDataPlus (Identifier, LowDataPlus)]
  -> WithEnv LowDataPlus
exponentSigma lamThetaName ml mxts = do
  penv <- gets codeEnv
  let sigmaExp = (ml, LowDataTheta lamThetaName)
  case lookup lamThetaName penv of
    Just _ -> return sigmaExp
    Nothing -> do
      xts <- mapM supplyName mxts
      (countVarName, countVar) <- newLowDataUpsilon
      (sigVarName, sigVar) <- newLowDataUpsilon
      let appList =
            map
              (\(x, t) ->
                 ( ml
                 , LowCodePiElimDownElim
                     t
                     [ (Nothing, LowCodeUpIntro countVar)
                     , (Nothing, LowCodeUpIntro $ toLowDataUpsilon (x, fst t))
                     ]))
              xts
      ys <- mapM (const $ newNameWith "var") xts
      let ys' = map toLowDataUpsilon' ys
      cont <-
        bindLetLowCode (zip ys appList) (ml, LowCodeTransposeN countVar ys')
      let lamBody = (ml, LowCodeSigmaElim (map fst xts) sigVar cont)
      insLowCodeEnv lamThetaName [countVarName, sigVarName] lamBody
      return sigmaExp

bindLetLowCode ::
     [(Identifier, LowCodePlus)] -> LowCodePlus -> WithEnv LowCodePlus
bindLetLowCode [] cont = return cont
bindLetLowCode ((x, e):xes) cont = do
  e' <- bindLetLowCode xes cont
  upElim (fst e') x e e'

upElim ::
     Maybe Loc
  -> Identifier
  -> LowCodePlus
  -> LowCodePlus
  -> WithEnv LowCodePlus
upElim ml x e1 e2 = do
  lamThetaName <- newNameWith "lam"
  insLowCodeEnv lamThetaName [x] e2
  return (ml, LowCodePiElimDownElim (ml, LowDataTheta lamThetaName) [e1])

newLowDataUpsilon :: WithEnv (Identifier, LowDataPlus)
newLowDataUpsilon = do
  x <- newNameWith "arg"
  return (x, (Nothing, LowDataUpsilon x))

asLowType :: DataPlus -> WithEnv LowType
asLowType t =
  case t of
    (_, DataEpsilon x) -> return $ asLowType' x
    _                  -> throwError "expandData.epsilon-intro"

asLowType' :: Identifier -> LowType
asLowType' x
  | Just ('i', numStr) <- destructMaybe x
  , Just i <- readMaybe numStr = LowTypeSignedInt i
  | Just ('u', numStr) <- destructMaybe x
  , Just i <- readMaybe numStr = LowTypeUnsignedInt i
  | Just ('f', numStr) <- destructMaybe x
  , Just i <- readMaybe numStr = LowTypeFloat i
  | otherwise = LowTypeSignedInt 64

destructMaybe :: [a] -> Maybe (a, [a])
destructMaybe []     = Nothing
destructMaybe (x:xs) = Just (x, xs)
