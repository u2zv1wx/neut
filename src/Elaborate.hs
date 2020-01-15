{-# LANGUAGE OverloadedStrings #-}

module Elaborate
  ( elaborate
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.List (nub)
import Numeric.Half

import qualified Data.HashMap.Strict as Map
import qualified Data.Text as T

import Data.Basic
import Data.Env
import Data.Term
import Data.WeakTerm
import Elaborate.Analyze
import Elaborate.Infer
import Elaborate.Synthesize
import Reduce.Term
import Reduce.WeakTerm

-- import Reduce.WeakTerm
-- Given a term `e` and its name `main`, this function
--   (1) traces `e` using `infer e`, collecting type constraints,
--   (2) updates weakTypeEnv for `main` by the result of `infer e`,
--   (3) analyze the constraints, solving easy ones,
--   (4) synthesize these analyzed constraints, solving as many solutions as possible,
--   (5) elaborate the given term using the result of synthesis.
-- The inference algorithm in this module is based on L. de Moura, J. Avigad,
-- S. Kong, and C. Roux. "Elaboration in Dependent Type Theory", arxiv,
-- https://arxiv.org/abs/1505.04324, 2015.
elaborate :: WeakTermPlus -> WithEnv TermPlus
elaborate e
  -- p "infer"
 = do
  e' <- infer e
  -- p "analyze/synthesize"
  -- Kantian type-inference ;)
  -- gets constraintEnv >>= analyze >>= synthesize
  analyze
  synthesize
  -- p "done"
  reduceSubstEnv
  -- p "elaborate"
  -- this reduceTermPlus is necessary since e' contains "DONT_CARE" in its
  -- type of arguments of abstractions of meta-variables.
  e'' <- elaborate' e' >>= reduceTermPlus
  return e''
  -- let info2 = toInfo "elaborated term is not closed:" e''
  -- assertMP info2 (return e'') $ null (varTermPlus e'')

-- This function translates a well-typed term into an untyped term in a
-- reduction-preserving way. Here, we translate types into units (nullary product).
-- This doesn't cause any problem since types doesn't have any beta-reduction.
elaborate' :: WeakTermPlus -> WithEnv TermPlus
elaborate' (m, WeakTermTau) = do
  return (m, TermTau)
elaborate' (m, WeakTermUpsilon x) = do
  return (m, TermUpsilon x)
elaborate' (m, WeakTermPi xts t) = do
  xts' <- mapM elaboratePlus xts
  t' <- elaborate' t
  return (m, TermPi xts' t')
elaborate' (m, WeakTermPiIntro xts e) = do
  e' <- elaborate' e
  xts' <- mapM elaboratePlus xts
  return (m, TermPiIntro xts' e')
elaborate' (m, WeakTermPiElim e es) = do
  e' <- elaborate' e
  es' <- mapM elaborate' es
  return (m, TermPiElim e' es')
elaborate' (m, WeakTermIter (x, t) xts e) = do
  t' <- elaborate' t
  xts' <- mapM elaboratePlus xts
  e' <- elaborate' e
  return (m, TermIter (x, t') xts' e')
elaborate' (_, WeakTermZeta x) = do
  sub <- gets substEnv
  case Map.lookup x sub of
    Nothing -> throwError $ "elaborate' i: remaining hole: " <> x
    Just e -> do
      e' <- elaborate' e
      return e'
elaborate' (m, WeakTermConst x) = do
  mi <- elaborateIsEnum x
  case mi of
    Nothing -> return (m, TermConst x)
    Just i -> return (m, TermIntU 64 i)
elaborate' (m, WeakTermConstDecl (x, t) e) = do
  t' <- elaborate' t
  e' <- elaborate' e
  return (m, TermConstDecl (x, t') e')
elaborate' (m, WeakTermIntS size x) = do
  return (m, TermIntS size x)
elaborate' (m, WeakTermIntU size x) = do
  return (m, TermIntU size x)
elaborate' (m, WeakTermInt t x) = do
  t' <- elaborate' t >>= reduceTermPlus
  case t' of
    (_, TermConst intType) ->
      case asLowTypeMaybe intType of
        Just (LowTypeIntS size) -> return (m, TermIntS size x)
        Just (LowTypeIntU size) -> return (m, TermIntU size x)
        _ ->
          throwError $ T.pack (show x) <> " should be int, but is " <> intType
    _ -> throwError $ "elaborate.WeakTermInt."
elaborate' (m, WeakTermFloat16 x) = do
  return (m, TermFloat16 x)
elaborate' (m, WeakTermFloat32 x) = do
  return (m, TermFloat32 x)
elaborate' (m, WeakTermFloat64 x) = do
  return (m, TermFloat64 x)
elaborate' (m, WeakTermFloat t x) = do
  t' <- elaborate' t >>= reduceTermPlus
  case t' of
    (_, TermConst floatType) -> do
      let x16 = realToFrac x :: Half
      let x32 = realToFrac x :: Float
      case asLowTypeMaybe floatType of
        Just (LowTypeFloat FloatSize16) -> return (m, TermFloat16 x16)
        Just (LowTypeFloat FloatSize32) -> return (m, TermFloat32 x32)
        Just (LowTypeFloat FloatSize64) -> return (m, TermFloat64 x)
        _ ->
          throwError $
          T.pack (show x) <> " should be float, but is " <> floatType
    _ -> throwError "elaborate.WeakTermFloat"
elaborate' (m, WeakTermEnum k) = do
  return (m, TermEnum k)
elaborate' (m, WeakTermEnumIntro x) = do
  return (m, TermEnumIntro x)
elaborate' (m, WeakTermEnumElim (e, t) les) = do
  e' <- elaborate' e
  les' <- forM les elaboratePlus
  t' <- elaborate' t >>= reduceTermPlus
  case t' of
    (_, TermEnum x) -> do
      caseCheckEnumIdentifier x $ map fst les
      return (m, TermEnumElim e' les')
    _ -> throwError "type error (enum elim)"
elaborate' (m, WeakTermArray k indexType) = do
  indexType' <- elaborate' indexType
  return (m, TermArray k indexType')
elaborate' (m, WeakTermArrayIntro k les) = do
  let (ls, es) = unzip les
  es' <- mapM elaborate' es
  return (m, TermArrayIntro k (zip ls es'))
elaborate' (m, WeakTermArrayElim k e1 e2) = do
  e1' <- elaborate' e1
  e2' <- elaborate' e2
  return (m, TermArrayElim k e1' e2')

elaboratePlus :: (a, WeakTermPlus) -> WithEnv (a, TermPlus)
elaboratePlus (x, t) = do
  t' <- elaborate' t
  return (x, t')

-- enum.n{i}   ~> Just i
-- enum.choice ~> Just 2 (assuming choice = {left, right})
-- otherwise   ~> Nothing
elaborateIsEnum :: Identifier -> WithEnv (Maybe Integer)
elaborateIsEnum x
  | Just i <- asEnumNatNumConstant x = return $ Just i
elaborateIsEnum x
  | ["enum", enumStr] <- wordsBy '.' x = do
    b <- isDefinedEnum enumStr
    if not b
      then return Nothing
      else do
        ls <- lookupEnumSet enumStr
        return $ Just $ toInteger $ length ls
elaborateIsEnum _ = return Nothing

caseCheckEnumIdentifier :: EnumType -> [Case] -> WithEnv ()
caseCheckEnumIdentifier (EnumTypeLabel x) labelList = do
  ls <- lookupEnumSet x
  caseCheckEnumIdentifier' (toInteger $ length ls) labelList
caseCheckEnumIdentifier (EnumTypeNatNum i) labelList = do
  caseCheckEnumIdentifier' i labelList

caseCheckEnumIdentifier' :: Integer -> [Case] -> WithEnv ()
caseCheckEnumIdentifier' i labelList = do
  let len = toInteger $ length (nub labelList)
  if i <= len || CaseDefault `elem` labelList
    then return ()
    else throwError "non-exhaustive pattern"

lookupEnumSet :: Identifier -> WithEnv [Identifier]
lookupEnumSet name = do
  eenv <- gets enumEnv
  case Map.lookup name eenv of
    Nothing -> throwError $ "no such enum defined: " <> name
    Just ls -> return ls

reduceSubstEnv :: WithEnv ()
reduceSubstEnv = do
  senv <- gets substEnv
  let senv' = Map.map reduceWeakTermPlus senv
  modify (\env -> env {substEnv = senv'})
