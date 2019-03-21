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

modalPos :: Pos -> WithEnv Value
modalPos (PosVar x) = return $ ValueVar x
modalPos (PosConst x) = return $ ValueConst x
modalPos (PosSigma xts) = do
  let (xs, ts) = unzip xts
  ts' <- mapM modalPos ts
  return $ ValueSigma (zip xs ts')
modalPos (PosSigmaIntro es) = do
  ds <- mapM modalPos es
  return $ ValueSigmaIntro ds
modalPos (PosIndex l) = return $ ValueIndex l
modalPos (PosIndexIntro l meta) = return $ ValueIndexIntro l meta
modalPos (PosDown t) = do
  t' <- modalNeg t
  return $ ValueDown t'
modalPos (PosDownIntro e) = do
  let (body, args) = toNegPiIntroSeq e
  body' <- modalNeg body
  thunkName <- newNameWith "thunk"
  insModalEnv thunkName args body'
  return $ ValueVar thunkName
modalPos PosUniv = return ValueUniv

modalNeg :: Neg -> WithEnv Comp
modalNeg (NegPi (x, tdom) tcod) = do
  tdom' <- modalPos tdom
  tcod' <- modalNeg tcod
  return $ CompPi (x, tdom') tcod'
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
modalNeg (NegUp v) = do
  v' <- modalPos v
  return $ CompUp v'
modalNeg (NegUpIntro v) = do
  v' <- modalPos v
  return $ CompUpIntro v'
modalNeg (NegUpElim x e1 e2) = do
  e1' <- modalNeg e1
  e2' <- modalNeg e2
  return $ CompUpElim x e1' e2'
modalNeg (NegDownElim e) = do
  e' <- modalPos e
  thunkName <- newNameWith "thunk"
  bindLet [(thunkName, e')] $ CompPiElimDownElim thunkName []
modalNeg (NegMu x e) = do
  let (body, args) = toNegPiIntroSeq e
  body' <- modalNeg body
  insModalEnv x args body'
  return $ CompPiElimDownElim x []

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
