-- Before describing the behavior of this module, we firstly define *modal-normal form*.
-- A polarized term is in *modal-normal form* if the following conditions are true:
-- (A) for every application `e @ v1 @ ... @ vn`,
--   - e == (constElim x) for some variable x,
--   - vi == xi for some variable x,
-- (B) the term doesn't contain any thunk/force, box/unbox.
-- (C) for every unboxing `(constElim v)`, v == x for some variable x.
--
-- Now, this module (1) eliminates `down N` (the type of closures) and `box N` (the type of
-- functions), (2) translates a term to modal-normal form.
--
-- For (1), we treat `box N` as `down N`, and employ the following type isomorphism:
--   Down N === Sigma (P : Type). Const (P -> N) * P.
-- One may understand that this is a proof-theoretic characterization of closure conversion.
--
-- For (2), we *crop* closed term in appropriate situation, insert it into the environment,
-- and replace the original term as a variable.
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
    liftIO $ putStrLn $ show args
    liftIO $ putStrLn $ Pr.ppShow e
    liftIO $ putStrLn "-----------------------------"

modalPos :: Pos -> WithEnv Value
modalPos (PosVar x) = return $ ValueVar x
modalPos (PosSigmaIntro es) = do
  ds <- mapM modalPos es
  return $ ValueSigmaIntro ds
modalPos (PosIndexIntro l meta) = return $ ValueIndexIntro l meta
modalPos (PosDownIntro e) = do
  menv <- gets modalEnv
  let ds = map fst menv
  clsName <- newNameWith "closure"
  makeClosure ds clsName e

modalNeg :: Neg -> WithEnv Comp
modalNeg lam@(NegPiIntro _ _) = modalNeg $ NegDownElim $ PosDownIntro lam
modalNeg app@(NegPiElim _ _) = do
  let (fun, args) = toNegPiElimSeq app
  fun' <- modalNeg fun
  args' <- mapM modalPos args
  xs <- mapM (const (newNameWith "arg")) args
  app' <- commPiElim fun' xs
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
modalNeg (NegDownElim e) = modalPos e >>= callClosure
modalNeg (NegConstElim x es) = do
  es' <- mapM modalPos es
  xs <- mapM (const (newNameWith "arg")) es
  bindLet (zip xs es') $ CompConstElim x xs
modalNeg (NegMu x e) = do
  menv <- gets modalEnv
  let ds = x : map fst menv
  makeClosure ds x e >>= callClosure

bindLet :: [(Identifier, Value)] -> Comp -> WithEnv Comp
bindLet [] e = return e
bindLet ((x, v):rest) e = do
  e' <- bindLet rest e
  return $ CompUpElim x (CompUpIntro v) e'

-- Commutative conversion for pi-elimination
commPiElim :: Comp -> [Identifier] -> WithEnv Comp
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

makeClosure :: [Identifier] -> Identifier -> Neg -> WithEnv Value
makeClosure definedVarList clsName e = do
  let (body, args) = toNegPiIntroSeq e
  penv <- gets polEnv
  let fvs = filter (`notElem` definedVarList ++ map fst penv) $ nub $ varNeg e
  envName <- newNameWith "env"
  body' <- modalNeg $ NegSigmaElim (PosVar envName) fvs body
  insModalEnv clsName (envName : args) body'
  let vs = map ValueVar fvs
  return $ ValueSigmaIntro [ValueVar clsName, ValueSigmaIntro vs]

callClosure :: Value -> WithEnv Comp
callClosure e = do
  envName <- newNameWith "env"
  clsName <- newNameWith "cls"
  return $
    CompSigmaElim e [clsName, envName] (CompPiElimDownElim clsName [envName])

varPos :: Pos -> [Identifier]
varPos (PosVar s) = [s]
varPos (PosSigmaIntro es) = concatMap varPos es
varPos (PosIndexIntro _ _) = []
varPos (PosDownIntro e) = varNeg e

varNeg :: Neg -> [Identifier]
varNeg (NegPiIntro x e) = do
  let vs = varNeg e
  filter (/= x) vs
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
varNeg (NegMu x e) = filter (/= x) $ varNeg e
