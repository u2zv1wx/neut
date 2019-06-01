module Closure
  ( closure
  , closurePos
  , closureNeg
  ) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans.Except

import Data.List

import Data
import Reduce
import Util

import Control.Comonad.Cofree

import qualified Text.Show.Pretty as Pr

import Debug.Trace

closure :: WithEnv ()
closure = do
  penv <- gets polEnv
  forM_ penv $ \(name, e) -> do
    e' <- closureNeg e
    insSPolEnv name e'

closurePos :: Pos -> WithEnv SPos
closurePos (PosVar x) = return $ SPosVar x
closurePos (PosConst x) = return $ SPosConst x
closurePos (PosSigmaIntro es) = do
  es' <- mapM closurePos es
  return $ SPosSigmaIntro es'
closurePos (PosIndexIntro l meta) = return $ SPosIndexIntro l meta
closurePos (PosDownIntro e) = do
  let fvs = nub $ varNeg e
  envName <- newNameWith "env"
  e' <- closureNeg e
  let lam = SNegPiIntro envName $ SNegSigmaElim (SPosVar envName) fvs e'
  return $ SPosSigmaIntro [SPosBoxIntro lam, SPosSigmaIntro $ map SPosVar fvs]
closurePos (PosBoxIntro e) = do
  e' <- closureNeg e
  return $ SPosBoxIntro e'

closureNeg :: Neg -> WithEnv SNeg
closureNeg (NegPiIntro x e) = do
  e' <- closureNeg e
  return $ SNegPiIntro x e'
closureNeg (NegPiElim e1 e2) = do
  e1' <- closureNeg e1
  e2' <- closurePos e2
  return $ SNegPiElim e1' e2'
closureNeg (NegSigmaElim e1 xs e2) = do
  e1' <- closurePos e1
  e2' <- closureNeg e2
  return $ SNegSigmaElim e1' xs e2'
closureNeg (NegIndexElim e branchList) = do
  let (labelList, es) = unzip branchList
  es' <- mapM closureNeg es
  e' <- closurePos e
  return $ SNegIndexElim e' (zip labelList es')
closureNeg (NegUpIntro v) = do
  v' <- closurePos v
  return $ SNegUpIntro v'
closureNeg (NegUpElim x e1 e2) = do
  e1' <- closureNeg e1
  e2' <- closureNeg e2
  return $ SNegUpElim x e1' e2'
closureNeg (NegDownElim e) = do
  e' <- closurePos e
  envName <- newNameWith "env"
  clsName <- newNameWith "cls"
  return $
    SNegSigmaElim
      e'
      [clsName, envName]
      (SNegPiElim (SNegBoxElim (SPosVar clsName)) (SPosVar envName))
closureNeg (NegBoxElim e) = do
  e' <- closurePos e
  return $ SNegBoxElim e'
closureNeg (NegConstElim x es) = do
  es' <- mapM closurePos es
  return $ SNegConstElim x es'
