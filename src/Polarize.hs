-- This module "polarizes" a neutral term into a negative term. Operationally,
-- this corresponds to determination of the order of evaluation. In proof-theoretic
-- term, we translate a ordinary dependent calculus to a dependent variant of
-- Call-By-Push-Value, although this translation doesn't preserve types when the
-- given term includes dependent sigma-elimination. A detailed explanation of
-- Call-By-Push-Value can be found in P. Levy. "Call-by-Push-Value: A Subsuming
-- Paradigm". Ph. D. thesis, Queen Mary College, 2001.
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

import Data.List (nub)

import Text.Read (readMaybe)

import Data.Maybe (isJust, maybeToList)

polarize :: Identifier -> Term -> WithEnv ()
polarize name e = do
  e' <- polarize' e
  insPolEnv name e'

-- Essence:
--
--   lam x. e
--   ~> return (thunk (lam p. let (env, x) := p in let xs := env in e), xs)
--
--   e1 @ e2
--   ~> bind x <- e2 in
--      bind f <- e1 in
--      let (lam, fvs) := f in
--      (force lam) @ (fvs, x)
--
-- where `xs` is the free variables of `lam x. e`.
--
-- The key property here is: every function has exactly 1 argument.
-- Note that, for example, `i32 -> bool -> string` is translated into
-- the 1-ary function `↓(i32 -> ↑↓(bool -> ↑string))`. This property holds
-- even in dependent situation where the type of a function is,
-- for example, `Pi (x : i32). if x == 1 then i32 -> bool else i32 -> bool -> i32`.
polarize' :: Term -> WithEnv Neg
polarize' (TermVar x) = return $ NegUpIntro $ PosVar x
polarize' (TermConst x) = toDefinition x
polarize' (TermPiIntro x e) = do
  e' <- polarize' e
  makeClosure x e'
polarize' (TermPiElim (TermMu x e1) e2) = do
  e1' <- polarize' e1
  insPolEnv x e1'
  e2' <- polarize' e2
  z <- newNameWith "tmp"
  -- return $ NegUpElim z e2' $ NegPiElim (NegDownElim (PosConst x)) (PosVar z)
  return $ NegUpElim z e2' $ NegPiElimDownElim (PosConst x) (PosVar z)
  -- undefined
polarize' (TermPiElim e1 e2) = do
  e1' <- polarize' e1
  e2' <- polarize' e2
  callClosure e1' e2'
polarize' (TermSigmaIntro es) = do
  es' <- mapM polarize' es
  xs <- mapM (const (newNameWith "sigma")) es'
  return $ bindLet (zip xs es') $ NegUpIntro $ PosSigmaIntro (map PosVar xs)
polarize' (TermSigmaElim e1 xs e2) = do
  e1' <- polarize' e1
  e2' <- polarize' e2
  z <- newNameWith "sigma"
  return $ NegUpElim z e1' (NegSigmaElim (PosVar z) xs e2')
polarize' (TermIndexIntro l t) = return $ NegUpIntro (PosIndexIntro l t)
polarize' (TermIndexElim e branchList) = do
  let (labelList, es) = unzip branchList
  e' <- polarize' e
  x <- newNameWith "tmp"
  cs <- mapM polarize' es
  return $ NegUpElim x e' (NegIndexElim (PosVar x) (zip labelList cs))
polarize' (TermMu _ _) = lift $ throwE "TermMu outside TermPiElim"
  -- e' <- polarize' e
  -- insPolEnv x e'
  -- return $ NegDownElim (PosConst x)

bindLet :: [(Identifier, Neg)] -> Neg -> Neg
bindLet [] cont = cont
bindLet ((x, e):xes) cont = NegUpElim x e $ bindLet xes cont

makeClosure :: Identifier -> Neg -> WithEnv Neg
makeClosure x e = do
  let fvs = filter (/= x) $ nub $ varNeg e
  envName <- newNameWith "env"
  pairName <- newNameWith "pair"
  -- let thunkLam =
  --       PosDownIntro $
  --       NegPiIntro pairName $
  --       NegSigmaElim (PosVar pairName) [envName, x] $
  --       NegSigmaElim (PosVar envName) fvs e
  let thunkLam =
        PosDownIntroPiIntro pairName $
        NegSigmaElim (PosVar pairName) [envName, x] $
        NegSigmaElim (PosVar envName) fvs e
  return $ NegUpIntro $ PosSigmaIntro [thunkLam, PosSigmaIntro (map PosVar fvs)]

callClosure :: Neg -> Neg -> WithEnv Neg
callClosure cls arg = do
  argVar <- newNameWith "arg"
  clsVar <- newNameWith "fun"
  thunkLam <- newNameWith "down.elim.cls"
  envName <- newNameWith "down.elim.env"
  return $
    NegUpElim argVar arg $
    NegUpElim clsVar cls $
    NegSigmaElim (PosVar clsVar) [thunkLam, envName] $
    NegPiElimDownElim
      (PosVar clsVar)
      (PosSigmaIntro [PosVar envName, PosVar argVar])
  -- return $
  --   NegUpElim argVar arg $
  --   NegUpElim clsVar cls $
  --   NegSigmaElim (PosVar clsVar) [thunkLam, envName] $
  --   NegPiElim
  --     (NegDownElim (PosVar clsVar))
  --     (PosSigmaIntro [PosVar envName, PosVar argVar])
  -- return $
  --   NegSigmaElim
  --     v
  --     [clsName, envName]
  --     (NegPiElim (NegDownElim (PosVar clsName)) (PosVar envName))

-- insert (possibly) environment-specific definition of constant
toDefinition :: Identifier -> WithEnv Neg
toDefinition x
  | Just c <- getPrintConstant x = toPrintDefinition c
  | Just c <- getArithBinOpConstant x = toArithBinOpDefinition c
  | otherwise = return $ NegUpIntro $ PosConst x

toArithLowType :: Identifier -> Maybe LowType
toArithLowType x
  | not (null x)
  , Just y <- readMaybe $ tail x
  , y > 0 =
    case head x of
      'i' -> Just $ LowTypeSignedInt y
      'u' -> Just $ LowTypeUnsignedInt y
      'f' -> Just $ LowTypeFloat y
      _ -> Nothing
  | otherwise = Nothing

getPrintConstant :: Identifier -> Maybe Constant
getPrintConstant x = do
  let xs = wordsWhen (== '.') x
  if length xs == 3 && head xs == "core" && xs !! 2 == "print"
    then do
      lowType <- toArithLowType $ xs !! 1
      return $ ConstantPrint lowType
    else Nothing

toPrintDefinition :: Constant -> WithEnv Neg
toPrintDefinition c = do
  x <- newNameWith "arg"
  makeClosure x $ NegConstElim c [PosVar x]
  -- t <- thunk $ NegPiIntro x $ NegConstElim c [PosVar x]
  -- return $ NegUpIntro t

getArithBinOpConstant :: Identifier -> Maybe Constant
getArithBinOpConstant x = do
  let xs = wordsWhen (== '.') x
  if length xs == 3 && head xs == "core"
    then do
      lowType <- toArithLowType $ xs !! 1
      binOp <- toArithBinOp $ xs !! 2
      return $ ConstantArith lowType binOp
    else Nothing

toArithBinOp :: Identifier -> Maybe Arith
toArithBinOp "add" = Just ArithAdd
toArithBinOp "sub" = Just ArithSub
toArithBinOp "mul" = Just ArithMul
toArithBinOp "div" = Just ArithDiv
toArithBinOp _ = Nothing

toArithBinOpDefinition :: Constant -> WithEnv Neg
toArithBinOpDefinition c = do
  x <- newNameWith "arg1"
  y <- newNameWith "arg2"
  -- lamy <- thunk $ NegPiIntro y $ NegConstElim c [PosVar x, PosVar y]
  lamy <- makeClosure y $ NegConstElim c [PosVar x, PosVar y]
  makeClosure x lamy

wordsWhen :: (Char -> Bool) -> String -> [String]
wordsWhen p s =
  case dropWhile p s of
    "" -> []
    s' -> w : wordsWhen p s''
      where (w, s'') = break p s'
-- -- should perform alpha-conv?
-- commPiElim :: Neg -> Pos -> WithEnv Neg
-- commPiElim (NegSigmaElim v xs e) arg = do
--   e' <- commPiElim e arg
--   return $ NegSigmaElim v xs e'
-- commPiElim (NegIndexElim v branchList) arg = do
--   let (labelList, es) = unzip branchList
--   es' <- mapM (`commPiElim` arg) es
--   return $ NegIndexElim v (zip labelList es')
-- commPiElim (NegUpIntro _) _ = lift $ throwE "Modal.commPiElim: type error"
-- commPiElim (NegUpElim x e1 e2) arg = do
--   e2' <- commPiElim e2 arg
--   return $ NegUpElim x e1 e2'
-- commPiElim e v = return $ NegPiElim e v
