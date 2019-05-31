module Modal
  ( modalize
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

modalize :: WithEnv ()
modalize = do
  penv <- gets polEnv
  forM_ penv $ \(name, e) -> do
    e' <- modalNeg e
    insModalEnv name [] e'
  menv <- gets modalEnv
  forM_ menv $ \(name, (args, e)) -> do
    liftIO $ putStrLn name
    liftIO $ print args
    liftIO $ putStrLn $ Pr.ppShow e
    liftIO $ putStrLn "-----------------------------"

modalPos :: Pos -> WithEnv Value
modalPos (PosVar x) = return $ ValueVar x
modalPos (PosConst x) = return $ ValueConst x
modalPos (PosSigmaIntro es) = do
  ds <- mapM modalPos es
  return $ ValueSigmaIntro ds
modalPos (PosIndexIntro l meta) = return $ ValueIndexIntro l meta
modalPos (PosDownIntro e) = do
  let (body, args) = toNegPiIntroSeq e
  let fvs = nub $ varNeg e
  envName <- newNameWith "env"
  body' <- modalNeg $ NegSigmaElim (PosVar envName) fvs body
  clsName <- newNameWith "cls"
  insModalEnv clsName (envName : args) body'
  return $
    ValueSigmaIntro [ValueConst clsName, ValueSigmaIntro $ map ValueVar fvs]

modalNeg :: Neg -> WithEnv Comp
modalNeg lam@(NegPiIntro _ _) = do
  v <- modalPos $ PosDownIntro lam
  let fvs = varNeg lam
  k <- callClosure v
  commPiElim k [ValueSigmaIntro $ map ValueVar fvs]
modalNeg app@(NegPiElim _ _) = do
  let (fun, args) = toNegPiElimSeq app
  fun' <- modalNeg fun
  args' <- mapM modalPos args
  xs <- mapM (const (newNameWith "arg")) args
  app' <- commPiElim fun' $ map ValueVar xs
  bindLet (zip xs args') app'
modalNeg (NegSigmaElim e1 xs e2) = do
  e1' <- modalPos e1
  e2' <- modalNeg e2
  return $ CompSigmaElim e1' xs e2'
modalNeg (NegIndexElim e branchList) = do
  let (labelList, es) = unzip branchList
  es' <- mapM modalNeg es
  e' <- modalPos e
  return $ CompIndexElim e' (zip labelList es')
modalNeg (NegUpIntro v) = do
  v' <- modalPos v
  return $ CompUpIntro v'
modalNeg (NegUpElim x e1 e2) = do
  e1' <- modalNeg e1
  e2' <- modalNeg e2
  return $ CompUpElim x e1' e2'
modalNeg (NegDownElim e) = do
  e' <- modalPos e
  callClosure e'
modalNeg (NegConstElim x es) = do
  es' <- mapM modalPos es
  xs <- mapM (const (newNameWith "arg")) es
  bindLet (zip xs es') $ CompConstElim x xs

callClosure :: Value -> WithEnv Comp
callClosure e = do
  envName <- newNameWith "env"
  clsName <- newNameWith "cls"
  return $
    CompSigmaElim
      e
      [clsName, envName]
      (CompPiElimDownElim clsName [ValueVar envName])

bindLet :: [(Identifier, Value)] -> Comp -> WithEnv Comp
bindLet [] e = return e
bindLet ((x, v):rest) e = do
  e' <- bindLet rest e
  return $ CompUpElim x (CompUpIntro v) e'

-- Commutative conversion for pi-elimination
commPiElim :: Comp -> [Value] -> WithEnv Comp
commPiElim (CompPiElimDownElim f xs) args =
  return $ CompPiElimDownElim f (xs ++ args)
commPiElim (CompSigmaElim v xs e) args = do
  e' <- commPiElim e args
  return $ CompSigmaElim v xs e'
commPiElim (CompIndexElim v branchList) args = do
  let (labelList, es) = unzip branchList
  es' <- mapM (`commPiElim` args) es
  return $ CompIndexElim v (zip labelList es')
commPiElim (CompUpElim x e1 e2) args = do
  e2' <- commPiElim e2 args
  return $ CompUpElim x e1 e2'
-- commPiElim (CompConstElim f xs) args = return $ CompConstElim f (xs ++ args)
commPiElim _ _ = lift $ throwE "Modal.commPiElim: type error"

toNegPiIntroSeq :: Neg -> (Neg, [Identifier])
toNegPiIntroSeq (NegPiIntro x body) = do
  let (body', args) = toNegPiIntroSeq body
  (body', x : args)
toNegPiIntroSeq t = (t, [])

toNegPiElimSeq :: Neg -> (Neg, [Pos])
toNegPiElimSeq (NegPiElim e1 e2) = do
  let (fun, xs) = toNegPiElimSeq e1
  (fun, e2 : xs)
toNegPiElimSeq c = (c, [])

varPos :: Pos -> [Identifier]
varPos (PosVar s) = [s]
varPos (PosConst _) = []
varPos (PosSigmaIntro es) = concatMap varPos es
varPos (PosIndexIntro _ _) = []
varPos (PosDownIntro e) = varNeg e

varNeg :: Neg -> [Identifier]
varNeg (NegPiIntro x e) = filter (/= x) $ varNeg e
varNeg (NegPiElim e1 e2) = varNeg e1 ++ varPos e2
varNeg (NegSigmaElim e1 xs e2) = do
  let vs1 = varPos e1
  let vs2 = filter (`notElem` xs) $ varNeg e2
  vs1 ++ vs2
varNeg (NegIndexElim e branchList) = do
  let vs1 = varPos e
  let vs2 = concatMap (varNeg . snd) branchList
  vs1 ++ vs2
varNeg (NegUpIntro e) = varPos e
varNeg (NegUpElim x e1 e2) = do
  let vs1 = varNeg e1
  let vs2 = filter (/= x) $ varNeg e2
  vs1 ++ vs2
varNeg (NegDownElim e) = varPos e
varNeg (NegConstElim _ es) = concatMap varPos es
