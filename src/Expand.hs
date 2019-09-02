-- Every type is converted into an "exponent", which is a function that receives
-- an integer `n` and a term `e` of that type, and returns n-copy of `e`, namely,
-- returns (e, ..., e). This operation roughly corresponds to eta-expansion. Indeed,
-- when the integer `n` equals to 1, this exponential operation degenerates to
-- eta-expansion.
module Expand where

import           Control.Monad.Except
import           Control.Monad.State
import           Prelude              hiding (pi)

import           Data.Basic
import           Data.Code
import           Data.Env
import           Data.LowCode

expandData :: DataPlus -> WithEnv LowDataPlus
expandData (_, DataTau) = exponentImmediate
expandData (m, DataTheta theta) = return (m, LowDataTheta theta)
expandData (m, DataUpsilon x) = return (m, LowDataUpsilon x)
expandData (_, DataEpsilon _) = exponentImmediate
expandData (m, DataEpsilonIntro l t) = do
  case t of
    _ -> undefined
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
expandCode (m, CodePiElimDownElim v vs) = do
  v' <- expandData v
  vs' <- mapM expandData vs
  return (m, LowCodePiElimDownElim v' vs')
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
expandCode (m, CodeUpElim x e1 e2) = do
  e1' <- expandCode e1
  e2' <- expandCode e2
  return (m, LowCodeUpElim x e1' e2')

expandTheta :: Theta -> WithEnv LowDataTheta
expandTheta = undefined

exponentImmediate :: WithEnv LowDataPlus
exponentImmediate = do
  penv <- gets polEnv
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
--     bind ysn = tn @ (m, yn) in -- ここまではコードとしてstaticに書ける
--     let (ys1-1, ..., ys1-m) := ys1 in -- ここでm-elimが必要になる。
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
  penv <- gets polEnv
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
                     [countVar, toLowDataUpsilon (x, fst t)]))
              xts
      ys <- mapM (const $ newNameWith "var") xts
      let ys' = map toLowDataUpsilon' ys
      let lamBody =
            ( ml
            , LowCodeSigmaElim
                (map fst xts)
                sigVar
                (bindLetLowCode
                   (zip ys appList)
                   (ml, LowCodeTransposeN countVar ys')))
      insLowCodeEnv lamThetaName [countVarName, sigVarName] lamBody
      return sigmaExp

bindLetLowCode :: [(Identifier, LowCodePlus)] -> LowCodePlus -> LowCodePlus
bindLetLowCode [] cont = cont
bindLetLowCode ((x, e):xes) cont = do
  let e' = bindLetLowCode xes cont
  (fst e', LowCodeUpElim x e e')

-- exponentClosure :: WithEnv LowDataPlus
-- exponentClosure = do
--   i <- exponentImmediate
--   (typeVarName, typeVar) <- newLowDataUpsilon
--   exponentSigma
--     "EXPONENT.CLOSURE"
--     Nothing
--     [Right (typeVarName, i), Left typeVar, Left i]
newLowDataUpsilon :: WithEnv (Identifier, LowDataPlus)
newLowDataUpsilon = newLowDataUpsilon' Nothing

newLowDataUpsilon' :: Maybe Loc -> WithEnv (Identifier, LowDataPlus)
newLowDataUpsilon' ml = do
  x <- newNameWith "arg"
  return (x, (ml, LowDataUpsilon x))
-- inline :: WithEnv ()
-- inline = do
--   penv <- gets polEnv
--   forM_ penv $ \(thetaName, (args, body)) -> do
--     body' <- inlineCodePlus body
--     unless (checkSanityCode body') $ throwError "sanity"
--     body'' <- processCode body'
--     insLowCodeEnv thetaName args body''
-- processData :: DataPlus -> WithEnv LowDataPlus
-- processData (_, DataImmediate)            = exponentImmediate
-- processData (_, DataTheta _)              = undefined
-- processData (_, DataUpsilon _)            = undefined
-- processData (_, DataEpsilon _)            = exponentImmediate
-- processData (_, DataEpsilonIntro _ _)     = undefined
-- processData (_, DataDownIntroPiIntro _ _) = undefined
-- processData (_, DataSigma xts)            = undefined
-- processData (_, DataSigmaIntro _)         = undefined
-- processCode :: CodePlus -> WithEnv LowCodePlus
-- processCode (m, CodeTheta theta) = do
--   theta' <- processTheta theta
--   return (m, LowCodeTheta theta')
-- processCode (_, CodeEpsilonElim {}) = undefined
-- processCode (_, CodePiElimDownElim {}) = undefined
-- processCode (_, CodeSigmaElim {}) = undefined
-- processCode (_, CodeUpIntro {}) = undefined
-- processCode (_, CodeUpElim {}) = undefined
-- processTheta :: Theta -> WithEnv LowDataTheta
-- processTheta = undefined
-- checkSanityData :: DataPlus -> Bool
-- checkSanityData (_, DataEpsilonIntro _ p) = null $ varDataPlus p
-- checkSanityData (_, DataSigma xts) = do
--   let (xs, ts) = unzip xts
--   all (`elem` xs) (concatMap varDataPlus ts) -- sigma must be closed
-- checkSanityData _ = True
-- checkSanityCode :: CodePlus -> Bool
-- checkSanityCode (_, CodeTheta _) = True
-- checkSanityCode (_, CodeEpsilonElim _ d branchList) = do
--   let (_, es) = unzip branchList
--   checkSanityData d && all checkSanityCode es
-- checkSanityCode (_, CodePiElimDownElim d ds) =
--   checkSanityData d && all checkSanityData ds
-- checkSanityCode (_, CodeSigmaElim _ v e) =
--   checkSanityData v && checkSanityCode e
-- checkSanityCode (_, CodeUpIntro v) = checkSanityData v
-- checkSanityCode (_, CodeUpElim _ e1 e2) =
--   checkSanityCode e1 && checkSanityCode e2
