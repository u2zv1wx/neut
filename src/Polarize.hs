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

-- Given a term, polarize it to a negative term. This translation determines the
-- order of evaluation. For example, an application `e1 @ e2` is tranlated into
--   let v := return (polarize' e1) in
--   let f := return (polarize' e2) in
--   (force f) @ v
-- Ignoring the `force`, one can see the order of evaluation is now made explicit.
polarize' :: Term -> WithEnv Neg
polarize' (TermVar x) = return $ NegDownElim (PosVar x)
polarize' (TermConst "core.i64.add") = arith "core.i64.add"
polarize' (TermConst "core.i64.sub") = arith "core.i64.sub"
polarize' (TermConst "core.i64.mul") = arith "core.i64.mul"
polarize' (TermConst "core.i64.div") = arith "core.i64.div"
polarize' (TermConst "core.i64.print") = do
  x <- newNameWith "lam"
  x' <- newNameWith "lam"
  return $
    NegPiIntro x $
    NegUpElim x' (NegDownElim (PosVar x)) $
    NegPiElim (NegDownElim (PosConst "core.i64.print")) (PosVar x')
polarize' (TermConst _) = undefined -- 定数ごとに異なる変換を行う
polarize' (TermPi (x, tdom) tcod) = do
  tdom' <- polarize' tdom
  tcod' <- polarize' tcod
  return $ NegUp (PosDown (NegPi (x, PosDown tdom') tcod'))
polarize' (TermPiIntro x e) = do
  e' <- polarize' e
  return $ NegPiIntro x e'
polarize' (TermPiElim e1 e2) = do
  e1' <- polarize' e1
  e2' <- polarize' e2
  return $ NegPiElim e1' (PosDownIntro e2')
polarize' (TermSigma xts) = do
  let (xs, ts) = unzip xts
  ts' <- mapM polarize' ts
  return $ NegUp $ PosSigma $ zip xs (map PosDown ts')
polarize' (TermSigmaIntro es) = do
  es' <- mapM polarize' es
  return $ NegUpIntro $ PosSigmaIntro (map PosDownIntro es')
polarize' (TermSigmaElim e1 xs e2) = do
  e2' <- polarize' e2
  z <- newNameWith "sigma"
  bindSeq [(z, e1)] (NegSigmaElim (PosVar z) xs e2')
polarize' (TermIndex l) = return $ NegUpIntro (PosIndex l)
polarize' (TermIndexIntro l meta) = return $ NegUpIntro (PosIndexIntro l meta)
polarize' (TermIndexElim e branchList) = do
  let (labelList, es) = unzip branchList
  cs <- mapM polarize' es
  x <- newNameWith "tmp"
  bindSeq [(x, e)] (NegIndexElim (PosVar x) (zip labelList cs))
polarize' (TermMu x e) = do
  e' <- polarize' e
  return $ NegMu x e'
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

arith :: Identifier -> WithEnv Neg
arith op = do
  x <- newNameWith "lam"
  x' <- newNameWith "lam"
  y <- newNameWith "lam"
  y' <- newNameWith "lam"
  return $
    NegPiIntro x $
    NegPiIntro y $
    NegUpElim x' (NegDownElim (PosVar x)) $
    NegUpElim y' (NegDownElim (PosVar y)) $
    NegPiElim (NegPiElim (NegDownElim (PosConst op)) (PosVar x')) (PosVar y')
