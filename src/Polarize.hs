-- This module "polarizes" a neutral term to a negative term. Operationally,
-- this corresponds to determination of the order of evaluation. In proof-theoretic
-- term, we translate a ordinary dependent calculus to a dependent variant of
-- Call-By-Push-Value calculus. The basics of Call-By-Push-Value can be found in
-- P. Levy. "Call-by-Push-Value: A Subsuming Paradigm". Ph. D. thesis, Queen
-- Mary College, 2001. In the thesis, Levy gives a translation from a call-by-value
-- calculus to a call-by-push-value calculus. Our translation is a dependent
-- extension of the translation. The crucial point in our translation would be that,
-- in dependent setting, the distinction between the type constructor `↑(-)`
-- and the term constructor `return (-)` seems to disappear. Indeed, in this
-- translation, we only use `NegUpIntro` (the term-level construct), and
-- not `NegUp` (the type-level construct).
module Polarize
  ( polarize
  ) where

import Control.Monad

import Control.Comonad.Cofree

import Control.Monad.State
import Control.Monad.Trans.Except

import qualified Text.Show.Pretty as Pr

import Data
import Reduce
import Util

import Data.Maybe (maybeToList)

-- Apply polarization to all the terms in `weakTermEnv`, and insert the results
-- to `polEnv`. This function also inserts the definitions of constants to `polEnv`.
polarize :: WithEnv ()
polarize = do
  tenv <- gets termEnv
  forM_ tenv $ \(name, e) -> do
    e' <- polarize' e >>= reduceNeg
    insPolEnv name e'
  insArith
  insCopyInt
  insPrintInt

-- Given a term, polarize it to a negative term. This translation determines the
-- order of evaluation. For example, an application `e1 @ e2` is tranlated into
--   let v := return (polarize' e1) in
--   let f := return (polarize' e2) in
--   (force f) @ v
-- Ignoring the `force`, one can see the order of evaluation is now made explicit.
polarize' :: Term -> WithEnv Neg
polarize' (TermVar x) = return $ NegUpIntro (PosVar x)
polarize' (TermPi (x, tdom) tcod) = do
  dom <- newNameWith "dom"
  cod <- newNameWith "cod"
  bindSeq
    [(dom, tdom), (cod, tcod)]
    (NegUpIntro (PosDown (NegPi (x, PosVar dom) (NegUpIntro (PosVar cod)))))
polarize' (TermPiIntro x e) = do
  e' <- polarize' e
  return $ NegUpIntro (PosDownIntro (NegPiIntro x e'))
polarize' (TermPiElim e1 e2) = do
  f <- newNameWith "pi"
  v <- newNameWith "arg"
  bindSeq [(v, e2), (f, e1)] (NegPiElim (NegDownElim (PosVar f)) (PosVar v))
polarize' tSigma@(TermSigma _ _)
  | (body, xts) <- toSigmaSeqTerm tSigma = do
    let (xs, ts) = unzip xts
    ys <- mapM (const (newNameWith "sigma")) xts
    z <- newNameWith "sigma"
    bindSeq
      (zip (ys ++ [z]) (ts ++ [body]))
      (NegUpIntro (PosSigma (zip xs (map PosVar ys)) (PosVar z)))
polarize' (TermSigmaIntro es) = do
  nameList <- mapM (const newName) es
  bindSeq (zip nameList es) (NegUpIntro (PosSigmaIntro (map PosVar nameList)))
polarize' (TermSigmaElim e1 xs e2) = do
  e2' <- polarize' e2
  z <- newNameWith "sigma"
  bindSeq [(z, e1)] (NegSigmaElim (PosVar z) xs e2')
polarize' (TermBox e) = do
  e' <- polarize' e
  return $ NegUpIntro (PosBox e')
polarize' (TermBoxIntro e) = do
  e' <- polarize' e
  return $ NegUpIntro (PosBoxIntro e')
polarize' (TermBoxElim e) = do
  z <- newNameWith "box"
  bindSeq [(z, e)] (NegBoxElim $ PosVar z)
polarize' (TermIndex l) = return $ NegUpIntro (PosIndex l)
polarize' (TermIndexIntro l meta) = return $ NegUpIntro (PosIndexIntro l meta)
polarize' (TermIndexElim e branchList) = do
  let (labelList, es) = unzip branchList
  cs <- mapM polarize' es
  x <- newNameWith "tmp"
  bindSeq [(x, e)] (NegIndexElim (PosVar x) (zip labelList cs))
polarize' (TermVector t1 t2) = do
  x1 <- newNameWith "dom"
  x2 <- newNameWith "cod"
  bindSeq
    [(x1, t1), (x2, t2)]
    (NegUpIntro (PosDown (NegVector (PosVar x1) (NegUpIntro (PosVar x2)))))
polarize' (TermVectorIntro branchList) = do
  let (labelList, es) = unzip branchList
  cs <- mapM polarize' es
  return $ NegUpIntro $ PosDownIntro $ NegVectorIntro (zip labelList cs)
polarize' (TermVectorElim e1 e2) = do
  f <- newNameWith "vec"
  v <- newNameWith "index"
  bindSeq [(v, e2), (f, e1)] (NegVectorElim (NegDownElim (PosVar f)) (PosVar v))
polarize' (TermMu x e) = do
  e' <- polarize' e
  return $ NegMu x e'
polarize' (TermConst t) = do
  x <- newNameWith "const"
  bindSeq [(x, t)] $ NegUpIntro $ PosConst $ PosVar x
polarize' (TermConstIntro x) = return $ NegUpIntro (PosConstIntro x)
polarize' (TermConstElim e) = do
  x <- newNameWith "const"
  bindSeq [(x, e)] $ NegConstElim $ PosVar x
polarize' (TermUniv _) = return $ NegUpIntro PosUniv

-- Intuitively, `bindSeq [(x1, e1), (x2, e2)] e3` is:
--   let x1 = (polarize' e1) in
--   let x2 = (polarize' e2) in
--   e3.
bindSeq :: [(Identifier, Term)] -> Neg -> WithEnv Neg
bindSeq [] fun = return fun
bindSeq ((formalArg, arg):rest) fun = do
  arg' <- polarize' arg
  fun' <- bindSeq rest fun
  return $ NegUpElim formalArg arg' fun'

insArith :: WithEnv ()
insArith = do
  let numLowTypeList = intLowTypeList ++ floatLowTypeList
  forM_ numLowTypeList $ \numLowType -> do
    (x, y) <- prepareVariables numLowType
    let base e = rb $ rt $ NegPiIntro x $ rt $ NegPiIntro y $ NegUpIntro e
    let add = base $ PosArith (ArithAdd, numLowType) (PosVar x) (PosVar y)
    let sub = base $ PosArith (ArithSub, numLowType) (PosVar x) (PosVar y)
    let mul = base $ PosArith (ArithMul, numLowType) (PosVar x) (PosVar y)
    let div = base $ PosArith (ArithDiv, numLowType) (PosVar x) (PosVar y)
    insPolEnv ("core." ++ show numLowType ++ ".add") add
    insPolEnv ("core." ++ show numLowType ++ ".sub") sub
    insPolEnv ("core." ++ show numLowType ++ ".mul") mul
    insPolEnv ("core." ++ show numLowType ++ ".div") div

prepareVariables :: LowType -> WithEnv (Identifier, Identifier)
prepareVariables lowType = do
  x <- newNameWith "arg"
  y <- newNameWith "arg"
  meta <- newNameWith "meta"
  insTypeEnv x $ meta :< NeutIndex (show lowType)
  insTypeEnv y $ meta :< NeutIndex (show lowType)
  return (x, y)

insCopyInt :: WithEnv ()
insCopyInt =
  forM_ intLowTypeList $ \intLowType -> do
    x <- newNameWith "arg"
    let pair = PosSigmaIntro [PosVar x, PosVar x]
    let copy = rb $ rt $ NegPiIntro x $ NegUpIntro pair
    insPolEnv ("core." ++ show intLowType ++ ".copy") copy

insPrintInt :: WithEnv ()
insPrintInt =
  forM_ intLowTypeList $ \intLowType -> do
    x <- newNameWith "arg"
    let print = rb $ rt $ NegPiIntro x $ NegPrint intLowType (PosVar x)
    insPolEnv ("core." ++ show intLowType ++ ".print") print

rt :: Neg -> Neg
rt e = NegUpIntro $ PosDownIntro e

rb :: Neg -> Neg
rb e = NegUpIntro $ PosBoxIntro e
