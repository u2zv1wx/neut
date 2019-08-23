module Close
  ( closeCode
  ) where

import           Data.Basic
import           Data.Code
import           Data.Env
import           Data.List
import           Data.WeakCode

-- closure conversion: ↓N ~ Sigma (P : U). (Box (P -> N), P)
closeData :: WeakDataPlus -> WithEnv DataPlus
closeData (m, WeakDataTau) = do
  m' <- closeDataMeta m
  return (m', DataTau)
closeData (m, WeakDataUpsilon x) = do
  m' <- closeDataMeta m
  return (m', DataUpsilon x)
closeData (m, WeakDataEpsilon x) = do
  m' <- closeDataMeta m
  return (m', DataEpsilon x)
closeData (m, WeakDataEpsilonIntro l) = do
  m' <- closeDataMeta m
  return (m', DataEpsilonIntro l)
closeData (m, WeakDataSigma xps p) = do
  m' <- closeDataMeta m
  let (xs, ps) = unzip xps
  ps' <- mapM closeData ps
  p' <- closeData p
  return (m', DataSigma (zip xs ps') p')
closeData (m, WeakDataSigmaIntro vs) = do
  m' <- closeDataMeta m
  vs' <- mapM closeData vs
  return (m', DataSigmaIntro vs')
closeData (m, WeakDataDown n) = do
  m' <- closeDataMeta m
  n' <- closeCode n
  return (m', DataDown n')
closeData (_, WeakDataDownIntro _) = undefined

closeDataMeta :: WeakDataMeta -> WithEnv DataMeta
closeDataMeta (WeakDataMetaTerminal ml) = return $ DataMetaTerminal ml
closeDataMeta (WeakDataMetaNonTerminal t ml) = do
  t' <- closeData t
  return $ DataMetaNonTerminal t' ml

closeCode :: WeakCodePlus -> WithEnv CodePlus
closeCode (m, WeakCodeTau) = do
  m' <- closeCodeMeta m
  return (m', CodeTau)
closeCode (m, WeakCodeTheta theta) = do
  m' <- closeCodeMeta m
  theta' <- closeTheta theta
  return (m', CodeTheta theta')
closeCode (m, WeakCodeEpsilonElim (x, t) v bs) = do
  m' <- closeCodeMeta m
  t' <- closeData t
  v' <- closeData v
  let (cs, es) = unzip bs
  es' <- mapM closeCode es
  return (m', CodeEpsilonElim (x, t') v' (zip cs es'))
closeCode (m, WeakCodePi xps n) = do
  m' <- closeCodeMeta m
  let (xs, ps) = unzip xps
  ps' <- mapM closeData ps
  n' <- closeCode n
  return (m', CodePi (zip xs ps') n')
closeCode c@(_, WeakCodePiIntro _ _) =
  closeCode (undefined, WeakCodeDownElim (undefined, WeakDataDownIntro c))
closeCode (_, WeakCodePiElim _ _) = undefined
closeCode (m, WeakCodeSigmaElim xps v e) = do
  m' <- closeCodeMeta m
  let (xs, ps) = unzip xps
  ps' <- mapM closeData ps
  v' <- closeData v
  e' <- closeCode e
  return (m', CodeSigmaElim (zip xs ps') v' e')
closeCode (m, WeakCodeUp p) = do
  m' <- closeCodeMeta m
  p' <- closeData p
  return (m', CodeUp p')
closeCode (m, WeakCodeUpIntro v) = do
  m' <- closeCodeMeta m
  v' <- closeData v
  return (m', CodeUpIntro v')
closeCode (m, WeakCodeUpElim (x, p) e1 e2) = do
  m' <- closeCodeMeta m
  p' <- closeData p
  e1' <- closeCode e1
  e2' <- closeCode e2
  return (m', CodeUpElim (x, p') e1' e2')
closeCode (_, WeakCodeDownElim _) = undefined
closeCode (_, WeakCodeMu _ _) = undefined

closeCodeMeta :: WeakCodeMeta -> WithEnv CodeMeta
closeCodeMeta = undefined

closeTheta :: WeakTheta -> WithEnv Theta
closeTheta = undefined

makeClosure :: [(Identifier, DataPlus)] -> CodePlus -> WithEnv WeakCodePlus
makeClosure = undefined
  -- let lamBody = WeakCodeSigmaElim fvs (PosUpsilon envName) e
  -- -- lamVar == thunk (lam (envName, x1, ..., xn) lamBody)
  -- insPolEnv lamVar (envName : xs) lamBody
  -- let fvEnv = PosSigmaIntro $ map PosUpsilon fvs
  -- return $ WeakCodeUpIntro $ PosSigmaIntro [PosConst lamVar, fvEnv]

-- makeClosure xs e = do
--   let fvs = filter (`notElem` map fst xs) $ nub $ varCodePlus e
--   envName <- newNameWith "env"
--   lamVar <- newNameWith "lam"
--   undefined
callClosure :: WeakCodePlus -> [WeakCodePlus] -> WithEnv WeakCodePlus
callClosure = undefined
-- callClosure e es = do
--   argVarNameList <- mapM (const $ newNameWith "arg") es
--   clsVarName <- newNameWith "fun"
--   thunkLamVarName <- newNameWith "down.elim.cls"
--   envVarName <- newNameWith "down.elim.env"
--   undefined
  -- return $
  --   WeakCodeUpElim clsVarName e $
  --   bindLet (zip argVarNameList es) $
  --   WeakCodeSigmaElim [thunkLamVarName, envVarName] (PosUpsilon clsVarName) $
  --   WeakCodePiElimDownElim
  --     (PosUpsilon thunkLamVarName)
  --     (PosUpsilon envVarName : map PosUpsilon argVarNameList)
