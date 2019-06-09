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
    insPolEnv name $ DeclarationFun args e'
  polarize' mainTerm

-- CBV translation into CBPV + closure conversion
-- (In the result of this translation, every function has exactly 1 argument)
polarize' :: Term -> WithEnv Neg
polarize' (TermVar x) = return $ NegUpIntro $ PosVar x
polarize' (TermConst x) = toDefinition x
polarize' (TermPiIntro x e) = do
  e' <- polarize' e
  makeClosure x e'
polarize' (TermPiElim e1 e2) = do
  e1' <- polarize' e1
  e2' <- polarize' e2
  callClosure e1' e2'
polarize' (TermConstElim funName es) = do
  es' <- mapM polarize' es
  xs <- mapM (const (newNameWith "arg")) es'
  return $
    bindLet (zip xs es') $ NegPiElimDownElim (PosConst funName) (map PosVar xs)
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

bindLet :: [(Identifier, Neg)] -> Neg -> Neg
bindLet [] cont           = cont
bindLet ((x, e):xes) cont = NegUpElim x e $ bindLet xes cont

makeClosure :: Identifier -> Neg -> WithEnv Neg
makeClosure x e = NegUpIntro <$> makeClosure' x e

makeClosure' :: Identifier -> Neg -> WithEnv Pos
makeClosure' x e = do
  let fvs = filter (/= x) $ nub $ varNeg e
  envName <- newNameWith "env"
  lamVar <- newNameWith "lam"
  let lamBody = NegSigmaElim (PosVar envName) fvs e
  -- lamVar == thunk (lam (envName, x) lamBody)
  insPolEnv lamVar $ DeclarationFun [x, envName] lamBody
  let fvEnv = PosSigmaIntro $ map PosVar fvs
  return $ PosSigmaIntro [PosConst lamVar, fvEnv]

callClosure :: Neg -> Neg -> WithEnv Neg
callClosure cls arg = do
  argVarName <- newNameWith "arg"
  clsVarName <- newNameWith "fun"
  thunkLamVarName <- newNameWith "down.elim.cls"
  envVarName <- newNameWith "down.elim.env"
  return $
    NegUpElim argVarName arg $
    NegUpElim clsVarName cls $
    NegSigmaElim (PosVar clsVarName) [thunkLamVarName, envVarName] $
    NegPiElimDownElim
      (PosVar thunkLamVarName)
      [PosVar argVarName, PosVar envVarName]

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
  makeClosure x $ NegConstElim c [PosVar x]

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
  lamy <- makeClosure y $ NegConstElim c [PosVar x, PosVar y]
  makeClosure x lamy

wordsWhen :: (Char -> Bool) -> String -> [String]
wordsWhen p s =
  case dropWhile p s of
    "" -> []
    s' -> w : wordsWhen p s''
      where (w, s'') = break p s'
