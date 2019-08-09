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

import           Control.Monad.State
import           Data.List           (nub)
import           Text.Read           (readMaybe)

import           Data.Basic
import           Data.Env
import           Data.Polarized
import           Data.Term

polarize :: Term -> WithEnv Neg
polarize mainTerm = do
  tenv <- gets termEnv
  forM_ tenv $ \(name, (args, e)) -> do
    e' <- polarize' e
    insPolEnv name args e' -- name = thunk (lam args. e')
  polarize' mainTerm

-- CBV translation into CBPV + closure conversion
polarize' :: Term -> WithEnv Neg
polarize' (TermUpsilon x) = return $ NegUpIntro $ PosUpsilon x
polarize' (TermEpsilonIntro l t) = return $ NegUpIntro (PosEpsilonIntro l t)
polarize' (TermEpsilonElim x e branchList) = do
  let (labelList, es) = unzip branchList
  e' <- polarize' e
  cs <- mapM polarize' es
  return $ NegUpElim x e' (NegEpsilonElim (PosUpsilon x) (zip labelList cs))
polarize' (TermConst x) = toDefinition x
polarize' (TermPiIntro xs e) = do
  e' <- polarize' e
  makeClosure xs e'
polarize' (TermPiElim e es) = do
  e' <- polarize' e
  es' <- mapM polarize' es
  callClosure e' es'
polarize' (TermConstElim funName es) = do
  es' <- mapM polarize' es
  xs <- mapM (const (newNameWith "arg")) es'
  return $
    bindLet (zip xs es') $
    NegConstElim (ConstantLabel funName) (map PosUpsilon xs)
polarize' (TermSigmaIntro es) = do
  es' <- mapM polarize' es
  xs <- mapM (const (newNameWith "sigma")) es'
  return $ bindLet (zip xs es') $ NegUpIntro $ PosSigmaIntro (map PosUpsilon xs)
polarize' (TermSigmaElim xs e1 e2) = do
  e1' <- polarize' e1
  e2' <- polarize' e2
  z <- newNameWith "sigma"
  return $ NegUpElim z e1' (NegSigmaElim xs (PosUpsilon z) e2')

bindLet :: [(Identifier, Neg)] -> Neg -> Neg
bindLet [] cont           = cont
bindLet ((x, e):xes) cont = NegUpElim x e $ bindLet xes cont

makeClosure :: [Identifier] -> Neg -> WithEnv Neg
makeClosure xs e = do
  let fvs = filter (`notElem` xs) $ nub $ varNeg e
  envName <- newNameWith "env"
  lamVar <- newNameWith "lam"
  let lamBody = NegSigmaElim fvs (PosUpsilon envName) e
  -- lamVar == thunk (lam (envName, x1, ..., xn) lamBody)
  insPolEnv lamVar (envName : xs) lamBody
  let fvEnv = PosSigmaIntro $ map PosUpsilon fvs
  return $ NegUpIntro $ PosSigmaIntro [PosConst lamVar, fvEnv]

callClosure :: Neg -> [Neg] -> WithEnv Neg
callClosure e es = do
  argVarNameList <- mapM (const $ newNameWith "arg") es
  clsVarName <- newNameWith "fun"
  thunkLamVarName <- newNameWith "down.elim.cls"
  envVarName <- newNameWith "down.elim.env"
  return $
    NegUpElim clsVarName e $
    bindLet (zip argVarNameList es) $
    NegSigmaElim [thunkLamVarName, envVarName] (PosUpsilon clsVarName) $
    NegPiElimDownElim
      (PosUpsilon thunkLamVarName)
      (PosUpsilon envVarName : map PosUpsilon argVarNameList)

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
      _   -> Nothing
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
  makeClosure [x] $ NegConstElim c [PosUpsilon x]

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
toArithBinOp _     = Nothing

toArithBinOpDefinition :: Constant -> WithEnv Neg
toArithBinOpDefinition c = do
  x <- newNameWith "arg1"
  y <- newNameWith "arg2"
  lamy <- makeClosure [y] $ NegConstElim c [PosUpsilon x, PosUpsilon y]
  makeClosure [x] lamy

wordsWhen :: (Char -> Bool) -> String -> [String]
wordsWhen p s =
  case dropWhile p s of
    "" -> []
    s' -> w : wordsWhen p s''
      where (w, s'') = break p s'
