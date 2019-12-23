module Elaborate
  ( elaborate
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.IORef
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
  exhaust e' >>= elaborate'

-- This function translates a well-typed term into an untyped term in a
-- reduction-preserving way. Here, we translate types into units (nullary product).
-- This doesn't cause any problem since types doesn't have any beta-reduction.
elaborate' :: WeakTermPlus -> WithEnv TermPlus
elaborate' (m, WeakTermTau) = do
  m' <- toMeta m
  return (m', TermTau)
elaborate' (m, WeakTermTheta x) = do
  m' <- toMeta m
  return (m', TermTheta x)
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
  t <- reduceTermPlus $ obtainType m'
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
  t <- reduceTermPlus $ obtainType m'
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

exhaust :: WeakTermPlus -> WithEnv WeakTermPlus
exhaust e = do
  b <- exhaust' e
  if b
    then return e
    else throwError "non-exhaustive pattern"

-- FIXME: exhaust'はmetaも検査するべき
-- FIXME: exhaust'はTermに対して定義されるべき
-- FIXME: exhaustはunitを返すようにするべき
exhaust' :: WeakTermPlus -> WithEnv Bool
exhaust' (_, WeakTermTau) = return True
exhaust' (_, WeakTermTheta _) = return True
exhaust' (_, WeakTermUpsilon _) = return True
exhaust' (_, WeakTermPi xts t) = allM exhaust' $ t : map snd xts
exhaust' (_, WeakTermPiIntro _ e) = exhaust' e
exhaust' (_, WeakTermPiElim e es) = allM exhaust' $ e : es
exhaust' (_, WeakTermMu _ e) = exhaust' e
exhaust' (_, WeakTermZeta _) = return False
exhaust' (_, WeakTermIntS _ _) = return True
exhaust' (_, WeakTermIntU _ _) = return True
exhaust' (_, WeakTermInt _) = return True
exhaust' (_, WeakTermFloat16 _) = return True
exhaust' (_, WeakTermFloat32 _) = return True
exhaust' (_, WeakTermFloat64 _) = return True
exhaust' (_, WeakTermFloat _) = return True
exhaust' (_, WeakTermEnum _) = return True
exhaust' (_, WeakTermEnumIntro _) = return True
exhaust' (_, WeakTermEnumElim e branchList) = do
  b <- exhaust' e
  let labelList = map fst branchList
  t <- obtainType <$> (toMeta $ fst e)
  t' <- reduceTermPlus t
  case t' of
    (_, TermEnum x) -> exhaustEnumIdentifier x labelList b
    _ -> throwError "type error (exhaust)"
exhaust' (_, WeakTermArray _ dom cod) = allM exhaust' [dom, cod]
exhaust' (_, WeakTermArrayIntro _ les) = do
  let (_, es) = unzip les
  allM exhaust' es
exhaust' (_, WeakTermArrayElim _ e1 e2) = allM exhaust' [e1, e2]

exhaustEnumIdentifier :: EnumType -> [Case] -> Bool -> WithEnv Bool
exhaustEnumIdentifier (EnumTypeLabel x) labelList b1 = do
  eenv <- gets enumEnv
  case lookup x eenv of
    Nothing -> return $ CaseDefault `elem` labelList
    Just ls ->
      if length ls <= length (nub labelList)
        then return $ b1 && True
        else return False

allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM _ [] = return True
allM p (x:xs) = do
  b1 <- p x
  b2 <- allM p xs
  return $ b1 && b2

toMeta :: WeakMeta -> WithEnv Meta
toMeta (WeakMetaTerminal l) = return $ MetaTerminal l
toMeta (WeakMetaNonTerminal (Ref r) l) = do
  mt <- liftIO $ readIORef r
  case mt of
    Nothing -> throwError "found an unresolved type (compiler bug)"
    Just t -> do
      t' <- elaborate' t
      return $ MetaNonTerminal t' l

obtainType :: Meta -> TermPlus
obtainType (MetaTerminal _) = (MetaTerminal Nothing, TermTau)
obtainType (MetaNonTerminal t _) = t
