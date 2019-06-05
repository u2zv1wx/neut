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

polarize' :: Term -> WithEnv Neg
polarize' (TermVar x) = return $ NegUpIntro $ PosVar x
polarize' (TermConst x) = toDefinition x
polarize' (TermPiIntro x e) = do
  e' <- polarize' e
  lam <- thunk $ NegPiIntro x e'
  return $ NegUpIntro lam
polarize' (TermPiElim e1 e2) = do
  e1' <- polarize' e1
  e2' <- polarize' e2
  f <- newNameWith "fun"
  ff <- force $ PosVar f
  x <- newNameWith "arg"
  -- piElim <- commPiElim ff (PosVar x)
  -- return $ NegUpElim x e2' $ NegUpElim f e1' piElim
  return $ NegUpElim x e2' $ NegUpElim f e1' $ NegPiElim ff (PosVar x)
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
polarize' (TermMu x e) = do
  e' <- polarize' e
  insPolEnv x e'
  return $ NegDownElim (PosConst x)

bindLet :: [(Identifier, Neg)] -> Neg -> Neg
bindLet [] cont = cont
bindLet ((x, e):xes) cont = NegUpElim x e $ bindLet xes cont

thunk :: Neg -> WithEnv Pos
thunk e = do
  let fvs = nub $ varNeg e
  envName <- newNameWith "env"
  let lam = NegPiIntro envName $ NegSigmaElim (PosVar envName) fvs e
  return $ PosSigmaIntro [PosDownIntro lam, PosSigmaIntro $ map PosVar fvs]

force :: Pos -> WithEnv Neg
force v = do
  envName <- newNameWith "down.elim.env"
  clsName <- newNameWith "down.elim.cls"
  return $
    NegSigmaElim
      v
      [clsName, envName]
      (NegPiElim (NegDownElim (PosVar clsName)) (PosVar envName))

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
  t <- thunk $ NegPiIntro x $ NegConstElim c [PosVar x]
  return $ NegUpIntro t

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
  lamy <- thunk $ NegPiIntro y $ NegConstElim c [PosVar x, PosVar y]
  lamxy <- thunk $ NegPiIntro x $ NegUpIntro lamy
  return $ NegUpIntro lamxy

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
