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

import           Data.Basic
import           Data.Env
import           Data.Term
import           Data.WeakCode

polarize :: TermPlus -> WithEnv WeakCodePlus
polarize (_, TermTau) =
  return (undefined, WeakCodeUpIntro (undefined, WeakDataTau))
polarize (m, TermTheta x) = polarizeTheta m x
polarize (_, TermUpsilon x) =
  return (undefined, WeakCodeUpIntro (undefined, WeakDataUpsilon x))
polarize (_, TermEpsilon x) =
  return (undefined, WeakCodeUpIntro (undefined, WeakDataEpsilon x))
polarize (_, TermEpsilonIntro l) =
  return (undefined, WeakCodeUpIntro (undefined, WeakDataEpsilonIntro l))
polarize (_, TermEpsilonElim (x, _) e bs) = do
  let (cs, es) = unzip bs
  es' <- mapM polarize es
  e' <- polarize e
  y <- newNameWith "epsilon"
  return
    ( undefined
    , WeakCodeUpElim
        (y, undefined)
        e'
        ( undefined
        , WeakCodeEpsilonElim
            (x, undefined)
            (undefined, WeakDataUpsilon y)
            (zip cs es')))
polarize (_, TermPi xts t) = do
  let (xs, ts) = unzip xts
  ts' <- mapM polarize ts
  ys <- mapM (const $ newNameWith "pi") ts'
  t' <- polarize t
  ys' <- mapM undefined ys -- tovar
  bindLet
    (zip ys ts')
    ( undefined
    , WeakCodeUpIntro
        (undefined, WeakDataDown (undefined, WeakCodePi (zip xs ys') t')))
polarize (_, TermPiIntro xts e) = do
  let (xs, ts) = unzip xts
  ts' <- mapM polarize ts
  ys <- mapM (const $ newNameWith "lam") ts'
  ys' <- mapM undefined ys -- tovar
  e' <- polarize e
  bindLet
    (zip ys ts')
    ( undefined
    , WeakCodeUpIntro
        ( undefined
        , WeakDataDownIntro (undefined, WeakCodePiIntro (zip xs ys') e')))
polarize (_, TermPiElim e es) = do
  e' <- polarize e
  f <- newNameWith "fun"
  f' <- undefined f
  es' <- mapM polarize es
  xs <- mapM (const $ newNameWith "arg") es'
  xs' <- mapM undefined xs
  bindLet
    ((f, e') : zip xs es')
    (undefined, WeakCodePiElim (undefined, WeakCodeDownElim f') xs')
polarize (_, TermSigma xts) = do
  let (xs, ts) = unzip xts
  ts' <- mapM polarize ts
  ys <- mapM (const $ newNameWith "pi") ts'
  ys' <- mapM undefined ys -- tovar
  bindLet
    (zip ys ts')
    (undefined, WeakCodeUpIntro (undefined, WeakDataSigma (zip xs ys')))
polarize (_, TermSigmaIntro es) = do
  es' <- mapM polarize es
  xs <- mapM (const $ newNameWith "sigma") es'
  ys <- mapM undefined xs -- tovar
  bindLet
    (zip xs es')
    (undefined, WeakCodeUpIntro (undefined, WeakDataSigmaIntro ys))
polarize (_, TermSigmaElim xts e1 e2) = do
  e1' <- polarize e1
  z <- newNameWith "sigma"
  let (xs, ts) = unzip xts
  ts' <- mapM polarize ts
  ys <- mapM (const $ newNameWith "sigma") ts'
  z' <- undefined z -- toVar
  ys' <- mapM undefined ys -- toVar
  e2' <- polarize e2
  bindLet
    ((z, e1') : zip ys ts')
    (undefined, WeakCodeSigmaElim (zip xs ys') z' e2')
polarize (_, TermMu (x, t) e) = do
  k <- newNameWith "mu"
  e' <- polarize e
  t' <- polarize t
  y <- newNameWith "mu"
  y' <- undefined y
  bindLet [(k, e'), (y, t')] (undefined, WeakCodeMu (x, y') e')
  -- es' <- mapM polarize es
  -- xs <- mapM (const (newNameWith "sigma")) es'
  -- undefined
  -- return $
  --   bindLet (zip xs es') $
  --   WeakCodeUpIntro $ WeakDataSigmaIntro (map WeakDataUpsilon xs)
  -- let (labelList, es) = unzip branchList
  -- e' <- polarize e
  -- cs <- mapM polarize es
  -- undefined
  -- return $
  --   WeakCodeUpElim
  --     x
  --     e'
  --     (WeakCodeEpsilonElim (WeakDataUpsilon x) (zip labelList cs))
  -- WeakCodeUpElim x e $ bindLet xes cont

bindLet :: [(Identifier, WeakCodePlus)] -> WeakCodePlus -> WithEnv WeakCodePlus
bindLet = undefined

-- bindLet [] cont           = cont
-- bindLet ((x, e):xes) cont = undefined
-- expand definitions of constants
polarizeTheta :: Meta -> Identifier -> WithEnv WeakCodePlus
polarizeTheta _ _ = undefined
--   -- | Just c <- getPrintConstant x = toPrintDefinition c
--   -- | Just c <- getArithBinOpConstant x = toArithBinOpDefinition c
--   -- | otherwise = return $ WeakCodeUpIntro $ WeakDataConst x
-- toArithLowType :: Identifier -> Maybe LowType
-- toArithLowType x
--   | not (null x)
--   , Just y <- readMaybe $ tail x
--   , y > 0 =
--     case head x of
--       'i' -> Just $ LowTypeSignedInt y
--       'u' -> Just $ LowTypeUnsignedInt y
--       'f' -> Just $ LowTypeFloat y
--       _   -> Nothing
--   | otherwise = Nothing
-- getPrintConstant :: Identifier -> Maybe Constant
-- getPrintConstant x = do
--   let xs = wordsWhen (== '.') x
--   if length xs == 3 && head xs == "core" && xs !! 2 == "print"
--     then do
--       lowType <- toArithLowType $ xs !! 1
--       return $ ConstantPrint lowType
--     else Nothing
-- toPrintDefinition :: Constant -> WithEnv WeakCode
-- toPrintDefinition c = do
--   x <- newNameWith "arg"
--   undefined
--   -- makeClosure [x] $ WeakCodeConstElim c [WeakDataUpsilon x]
-- getArithBinOpConstant :: Identifier -> Maybe Constant
-- getArithBinOpConstant x = do
--   let xs = wordsWhen (== '.') x
--   if length xs == 3 && head xs == "core"
--     then do
--       lowType <- toArithLowType $ xs !! 1
--       binOp <- toArithBinOp $ xs !! 2
--       return $ ConstantArith lowType binOp
--     else Nothing
-- toArithBinOp :: Identifier -> Maybe Arith
-- toArithBinOp "add" = Just ArithAdd
-- toArithBinOp "sub" = Just ArithSub
-- toArithBinOp "mul" = Just ArithMul
-- toArithBinOp "div" = Just ArithDiv
-- toArithBinOp _     = Nothing
-- toArithBinOpDefinition :: Constant -> WithEnv WeakCode
-- toArithBinOpDefinition c = do
--   undefined
--   -- x <- newNameWith "arg1"
--   -- y <- newNameWith "arg2"
--   -- lamy <-
--   --   makeClosure [y] $ WeakCodeConstElim c [WeakDataUpsilon x, WeakDataUpsilon y]
--   -- makeClosure [x] lamy
-- wordsWhen :: (Char -> Bool) -> String -> [String]
-- wordsWhen p s =
--   case dropWhile p s of
--     "" -> []
--     s' -> w : wordsWhen p s''
--       where (w, s'') = break p s'
