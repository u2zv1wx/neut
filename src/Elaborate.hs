module Elaborate
  ( elaborate
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.List (nub)
import Numeric.Half

import Data.Basic
import Data.Env
import Data.Term
import Data.WeakTerm
import Elaborate.Analyze
import Elaborate.Infer
import Elaborate.Synthesize
import Reduce.Term

import qualified Text.Show.Pretty as Pr

-- Given a term `e` and its name `main`, this function
--   (1) traces `e` using `infer e`, collecting type constraints,
--   (2) updates typeEnv for `main` by the result of `infer e`,
--   (3) analyze the constraints, solving easy ones,
--   (4) synthesize these analyzed constraints, solving as many solutions as possible,
--   (5) elaborate the given term using the result of synthesis.
-- The inference algorithm in this module is based on L. de Moura, J. Avigad,
-- S. Kong, and C. Roux. "Elaboration in Dependent Type Theory", arxiv,
-- https://arxiv.org/abs/1505.04324, 2015.
elaborate :: WeakTermPlus -> WithEnv TermPlus
elaborate e = do
  _ <- infer [] e
  -- Kantian type-inference ;)
  gets constraintEnv >>= analyze
  gets constraintQueue >>= synthesize
  -- update the type environment by resulting substitution
  sub <- gets substEnv
  tenv <- gets typeEnv
  tenv' <- mapM (substWeakTermPlus sub) tenv
  modify (\env -> env {typeEnv = tenv'})
  -- elaborate `e` using the resulting substitution
  e' <- substWeakTermPlus sub e
  e'' <- elaborate' e'
  caseCheck e''
  return e''
  -- caseCheck e' >>= elaborate'

-- This function translates a well-typed term into an untyped term in a
-- reduction-preserving way. Here, we translate types into units (nullary product).
-- This doesn't cause any problem since types doesn't have any beta-reduction.
elaborate' :: WeakTermPlus -> WithEnv TermPlus
elaborate' (m, WeakTermTau) = do
  m' <- toMeta m
  return (m', TermTau)
elaborate' (m, WeakTermTheta x) = do
  m' <- toMeta m
  mi <- elaborateIsEnum x
  case mi of
    Nothing -> return (m', TermTheta x)
    Just i -> return (m', TermIntU 64 i)
elaborate' (m, WeakTermUpsilon x) = do
  m' <- toMeta m
  return (m', TermUpsilon x)
elaborate' (m, WeakTermPi xts t) = do
  m' <- toMeta m
  xts' <- mapM elaboratePlus xts
  t' <- elaborate' t
  return (m', TermPi xts' t')
elaborate' (m, WeakTermPiIntro xts e) = do
  m' <- toMeta m
  e' <- elaborate' e
  xts' <- mapM elaboratePlus xts
  return (m', TermPiIntro xts' e')
elaborate' (m, WeakTermPiElim e es) = do
  m' <- toMeta m
  e' <- elaborate' e
  es' <- mapM elaborate' es
  return (m', TermPiElim e' es')
elaborate' (m, WeakTermMu (x, t) e) = do
  t' <- elaborate' t >>= reduceTermPlus
  case t' of
    (_, TermPi _ _) -> do
      m' <- toMeta m
      e' <- elaborate' e
      return (m', TermMu (x, t') e')
    _ -> throwError "CBV recursion is allowed only for Pi-types"
elaborate' (_, WeakTermZeta x) = do
  sub <- gets substEnv
  case lookup x sub of
    Just e -> elaborate' e
    Nothing -> throwError $ "elaborate' i: remaining hole: " ++ x
elaborate' (m, WeakTermIntS size x) = do
  m' <- toMeta m
  return (m', TermIntS size x)
elaborate' (m, WeakTermIntU size x) = do
  m' <- toMeta m
  return (m', TermIntU size x)
elaborate' (m, WeakTermInt x) = do
  m' <- toMeta m
  t <- reduceTermPlus $ obtainTermType m'
  case t of
    (_, TermTheta intType) ->
      case asLowTypeMaybe intType of
        Just (LowTypeIntS size) -> return (m', TermIntS size x)
        Just (LowTypeIntU size) -> return (m', TermIntU size x)
        _ -> throwError $ show x ++ " should be int, but is " ++ intType
    _ -> throwError "elaborate.WeakTermInt"
elaborate' (m, WeakTermFloat16 x) = do
  m' <- toMeta m
  return (m', TermFloat16 x)
elaborate' (m, WeakTermFloat32 x) = do
  m' <- toMeta m
  return (m', TermFloat32 x)
elaborate' (m, WeakTermFloat64 x) = do
  m' <- toMeta m
  return (m', TermFloat64 x)
elaborate' (m, WeakTermFloat x) = do
  m' <- toMeta m
  t <- reduceTermPlus $ obtainTermType m'
  case t of
    (_, TermTheta floatType) -> do
      let x16 = realToFrac x :: Half
      let x32 = realToFrac x :: Float
      case asLowTypeMaybe floatType of
        Just (LowTypeFloat FloatSize16) -> return (m', TermFloat16 x16)
        Just (LowTypeFloat FloatSize32) -> return (m', TermFloat32 x32)
        Just (LowTypeFloat FloatSize64) -> return (m', TermFloat64 x)
        _ -> throwError $ show x ++ " should be float, but is " ++ floatType
    _ -> throwError "elaborate.WeakTermFloat"
elaborate' (m, WeakTermEnum k) = do
  m' <- toMeta m
  return (m', TermEnum k)
elaborate' (m, WeakTermEnumIntro x) = do
  m' <- toMeta m
  return (m', TermEnumIntro x)
elaborate' (m, WeakTermEnumElim e branchList) = do
  m' <- toMeta m
  e' <- elaborate' e
  branchList' <- forM branchList elaboratePlus
  return (m', TermEnumElim e' branchList')
elaborate' (m, WeakTermArray k dom cod) = do
  m' <- toMeta m
  dom' <- elaborate dom
  cod' <- elaborate cod
  return (m', TermArray k dom' cod')
elaborate' (m, WeakTermArrayIntro k les) = do
  m' <- toMeta m
  let (ls, es) = unzip les
  es' <- mapM elaborate' es
  return (m', TermArrayIntro k (zip ls es'))
elaborate' (m, WeakTermArrayElim k e1 e2) = do
  m' <- toMeta m
  e1' <- elaborate' e1
  e2' <- elaborate' e2
  return (m', TermArrayElim k e1' e2')

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

-- `caseCheck e` checks if all the case-lists appear in `e` are exhaustive.
caseCheck :: TermPlus -> WithEnv ()
caseCheck (m, TermTau) = caseCheckMeta m
caseCheck (m, TermTheta _) = caseCheckMeta m
caseCheck (m, TermUpsilon _) = caseCheckMeta m
caseCheck (m, TermPi xts t) =
  caseCheckMeta m >> (mapM_ caseCheck $ t : map snd xts)
caseCheck (m, TermPiIntro xts e) =
  caseCheckMeta m >> (mapM_ caseCheck $ e : map snd xts)
caseCheck (m, TermPiElim e es) = caseCheckMeta m >> (mapM_ caseCheck $ e : es)
caseCheck (m, TermMu (_, t) e) = caseCheckMeta m >> (mapM_ caseCheck [t, e])
caseCheck (m, TermIntS _ _) = caseCheckMeta m
caseCheck (m, TermIntU _ _) = caseCheckMeta m
caseCheck (m, TermFloat16 _) = caseCheckMeta m
caseCheck (m, TermFloat32 _) = caseCheckMeta m
caseCheck (m, TermFloat64 _) = caseCheckMeta m
caseCheck (m, TermEnum _) = caseCheckMeta m
caseCheck (m, TermEnumIntro _) = caseCheckMeta m
caseCheck (m, TermEnumElim e branchList) = do
  caseCheckMeta m
  let labelList = map fst branchList
  t' <- reduceTermPlus $ obtainTermType $ fst e
  case t' of
    (_, TermEnum x) -> caseCheckEnumIdentifier x labelList
    _ -> throwError "type error (caseCheck)"
caseCheck (m, TermArray _ dom cod) =
  caseCheckMeta m >> mapM_ caseCheck [dom, cod]
caseCheck (m, TermArrayIntro _ les) = do
  caseCheckMeta m
  let (_, es) = unzip les
  mapM_ caseCheck es
caseCheck (m, TermArrayElim _ e1 e2) =
  caseCheckMeta m >> mapM_ caseCheck [e1, e2]

caseCheckMeta :: Meta -> WithEnv ()
caseCheckMeta (MetaTerminal _) = return ()
caseCheckMeta (MetaNonTerminal t _) = caseCheck t

caseCheckEnumIdentifier :: EnumType -> [Case] -> WithEnv ()
caseCheckEnumIdentifier (EnumTypeLabel x) labelList = do
  ls <- lookupEnumSet x
  caseCheckEnumIdentifier' (length ls) labelList
caseCheckEnumIdentifier (EnumTypeNatNum i) labelList = do
  caseCheckEnumIdentifier' i labelList

caseCheckEnumIdentifier' :: Int -> [Case] -> WithEnv ()
caseCheckEnumIdentifier' i labelList =
  if i <= length (nub labelList) || CaseDefault `elem` labelList
    then return ()
    else throwError "non-exhaustive pattern"

toMeta :: WeakMeta -> WithEnv Meta
toMeta (WeakMetaTerminal l) = return $ MetaTerminal l
toMeta (WeakMetaNonTerminal (Right t) l) = do
  t' <- elaborate' t
  return $ MetaNonTerminal t' l
toMeta (WeakMetaNonTerminal (Left i) l) = do
  mt <- lookupSubstEnv i
  case mt of
    Nothing -> throwError "found an unresolved type (compiler bug)"
    Just t -> do
      t' <- elaborate' t
      return $ MetaNonTerminal t' l

obtainTermType :: Meta -> TermPlus
obtainTermType (MetaTerminal _) = (MetaTerminal Nothing, TermTau)
obtainTermType (MetaNonTerminal t _) = t
