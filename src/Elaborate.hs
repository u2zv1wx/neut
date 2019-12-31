module Elaborate
  ( elaborate
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.List (nub)
import Numeric.Half

import Data.Basic
import Data.Env
import Data.PreTerm
import Data.Term
import Data.WeakTerm
import Elaborate.Analyze
import Elaborate.Infer
import Elaborate.Synthesize
import Reduce.PreTerm
import Reduce.Term

import qualified Data.PQueue.Min as Q

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
elaborate e = do
  p "infer"
  e' <- infer [] e
  -- Kantian type-inference ;)
  p "analyze"
  cs <- gets constraintEnv
  p $ "size: " ++ show (length cs)
  q <- gets constraintEnv >>= analyze
  p "synthesize"
  p $ "size: " ++ show (Q.size q)
  -- p "q:"
  -- p' q
  -- p "synth. q:"
  -- p' $ map (\(Enriched pair _ _) -> pair) $ Q.toList q
  synthesize q
  -- gets constraintEnv >>= analyze >>= synthessize
  -- gets constraintQueue >>= synthesize
  p "ok"
  -- update the type environment by resulting substitution
  tenv <- gets weakTypeEnv
  tenv' <- mapM elaborate' tenv
  modify (\env -> env {typeEnv = tenv'})
  p "updated typeEnv"
  -- elaborate `e` using the resulting substitution
  e'' <- elaborate' e'
  return e''

-- This function translates a well-typed term into an untyped term in a
-- reduction-preserving way. Here, we translate types into units (nullary product).
-- This doesn't cause any problem since types doesn't have any beta-reduction.
elaborate' :: PreTermPlus -> WithEnv TermPlus
elaborate' (m, PreTermTau) = do
  m' <- toMeta m
  return (m', TermTau)
elaborate' (m, PreTermTheta x) = do
  m' <- toMeta m
  mi <- elaborateIsEnum x
  case mi of
    Nothing -> return (m', TermTheta x)
    Just i -> return (m', TermIntU 64 i)
elaborate' (m, PreTermUpsilon x) = do
  m' <- toMeta m
  return (m', TermUpsilon x)
elaborate' (m, PreTermPi xts t) = do
  m' <- toMeta m
  xts' <- mapM elaboratePlus xts
  t' <- elaborate' t
  return (m', TermPi xts' t')
elaborate' (m, PreTermPiIntro xts e) = do
  m' <- toMeta m
  e' <- elaborate' e
  xts' <- mapM elaboratePlus xts
  return (m', TermPiIntro xts' e')
elaborate' (m, PreTermPiElim e es) = do
  m' <- toMeta m
  e' <- elaborate' e
  es' <- mapM elaborate' es
  return (m', TermPiElim e' es')
elaborate' (m, PreTermMu (x, t) e) = do
  t' <- elaborate' t >>= reduceTermPlus
  case t' of
    (_, TermPi _ _) -> do
      m' <- toMeta m
      e' <- elaborate' e
      return (m', TermMu (x, t') e')
    _ -> throwError "CBV recursion is allowed only for Pi-types"
elaborate' (_, PreTermZeta x) = do
  sub <- gets substEnv
  case lookup x sub of
    Just e -> elaborate' e
    Nothing -> throwError $ "elaborate' i: remaining hole: " ++ x
elaborate' (m, PreTermIntS size x) = do
  m' <- toMeta m
  return (m', TermIntS size x)
elaborate' (m, PreTermIntU size x) = do
  m' <- toMeta m
  return (m', TermIntU size x)
elaborate' (m, PreTermInt x) = do
  m' <- toMeta m
  t <- reducePreTermPlus $ typeOf' m
  case t of
    (_, PreTermTheta intType) ->
      case asLowTypeMaybe intType of
        Just (LowTypeIntS size) -> return (m', TermIntS size x)
        Just (LowTypeIntU size) -> return (m', TermIntU size x)
        _ -> throwError $ show x ++ " should be int, but is " ++ intType
    _ -> throwError "elaborate.PreTermInt"
elaborate' (m, PreTermFloat16 x) = do
  m' <- toMeta m
  return (m', TermFloat16 x)
elaborate' (m, PreTermFloat32 x) = do
  m' <- toMeta m
  return (m', TermFloat32 x)
elaborate' (m, PreTermFloat64 x) = do
  m' <- toMeta m
  return (m', TermFloat64 x)
elaborate' (m, PreTermFloat x) = do
  m' <- toMeta m
  t <- reducePreTermPlus $ typeOf' m
  case t of
    (_, PreTermTheta floatType) -> do
      let x16 = realToFrac x :: Half
      let x32 = realToFrac x :: Float
      case asLowTypeMaybe floatType of
        Just (LowTypeFloat FloatSize16) -> return (m', TermFloat16 x16)
        Just (LowTypeFloat FloatSize32) -> return (m', TermFloat32 x32)
        Just (LowTypeFloat FloatSize64) -> return (m', TermFloat64 x)
        _ -> throwError $ show x ++ " should be float, but is " ++ floatType
    _ -> throwError "elaborate.PreTermFloat"
elaborate' (m, PreTermEnum k) = do
  m' <- toMeta m
  return (m', TermEnum k)
elaborate' (m, PreTermEnumIntro x) = do
  m' <- toMeta m
  return (m', TermEnumIntro x)
elaborate' (m, PreTermEnumElim e les) = do
  m' <- toMeta m
  e' <- elaborate' e
  les' <- forM les elaboratePlus
  t <- reducePreTermPlus $ typeOf e
  case t of
    (_, PreTermEnum x) -> do
      caseCheckEnumIdentifier x $ map fst les
      return (m', TermEnumElim e' les')
    _ -> throwError "type error (enum elim)"
elaborate' (m, PreTermArray k indexType) = do
  m' <- toMeta m
  indexType' <- elaborate' indexType
  return (m', TermArray k indexType')
elaborate' (m, PreTermArrayIntro k les) = do
  m' <- toMeta m
  let (ls, es) = unzip les
  es' <- mapM elaborate' es
  return (m', TermArrayIntro k (zip ls es'))
elaborate' (m, PreTermArrayElim k e1 e2) = do
  m' <- toMeta m
  e1' <- elaborate' e1
  e2' <- elaborate' e2
  return (m', TermArrayElim k e1' e2')

elaboratePlus :: (a, PreTermPlus) -> WithEnv (a, TermPlus)
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

toMeta :: PreMeta -> WithEnv Meta
toMeta (PreMetaTerminal l) = return $ Meta {metaLocation = l}
toMeta (PreMetaNonTerminal _ l) = return $ Meta {metaLocation = l}
