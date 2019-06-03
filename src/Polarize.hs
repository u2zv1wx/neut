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

import Data.List (nub)

import Text.Read (readMaybe)

import Data.Maybe (isJust, maybeToList)

polarize :: Identifier -> Term -> WithEnv ()
polarize name e = do
  e' <- polarize' e
  insPolEnv name e'
  -- insPolEnv name $ PosDownIntro e'

polarize' :: Term -> WithEnv Neg
polarize' (TermVar x) = force (PosVar x)
polarize' (TermConst x) = toDefinition x
polarize' (TermPiIntro x e) = do
  e' <- polarize' e
  return $ NegPiIntro x e'
polarize' (TermPiElim e1 e2) = do
  e1' <- polarize' e1
  e2' <- polarize' e2 >>= thunk
  return $ NegPiElim e1' e2'
polarize' (TermSigmaIntro es) = do
  es' <- mapM (polarize' >=> thunk) es
  return $ NegUpIntro $ PosSigmaIntro es'
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
  | otherwise = return $ NegDownElim (PosConst x)

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
  x <- newNameWith "lam"
  x' <- newNameWith "lam"
  return $
    NegPiIntro x $
    NegUpElim x' (NegDownElim (PosVar x)) $ NegConstElim c [PosVar x']

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
  x <- newNameWith "cls1"
  y <- newNameWith "cls2"
  x' <- newNameWith "arg1"
  y' <- newNameWith "arg2"
  return $
    NegPiIntro x $
    NegPiIntro y $
    NegUpElim x' (NegDownElim (PosVar x)) $
    NegUpElim y' (NegDownElim (PosVar y)) $
    NegConstElim c [PosVar x', PosVar y']

wordsWhen :: (Char -> Bool) -> String -> [String]
wordsWhen p s =
  case dropWhile p s of
    "" -> []
    s' -> w : wordsWhen p s''
      where (w, s'') = break p s'
