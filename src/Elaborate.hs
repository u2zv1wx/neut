{-# LANGUAGE OverloadedStrings #-}

module Elaborate
  ( elaborate
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.List (nub)
import Numeric.Half
import System.Console.ANSI

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
  -- Kantian type-inference ;)
  -- gets constraintEnv >>= analyze >>= synthesize
  -- cs <- gets constraintEnv
  -- prepareInvRename
  -- forM_ cs $ \(x, y)
  --   -- x' <- invRename x
  --   -- y' <- invRename y
  --  -> do
  --   when (x /= y) $ do
  --     liftIO $ putStr "- "
  --     liftIO $ TIO.putStrLn $ toText x
  --     liftIO $ putStr "- "
  --     liftIO $ TIO.putStrLn $ toText y
  --     liftIO $ putStrLn "------"
  -- p' $ map (\(x, y) -> (toText x, toText y)) cs
  analyze
  synthesize
  -- p "done"
  reduceSubstEnv
  -- p "elaborate"
  -- this reduceTermPlus is necessary since e' contains "DONT_CARE" in its
  -- type of arguments of abstractions of meta-variables.
  e'' <- elaborate' e' >>= reduceTermPlus
  -- p' e''
  -- error "finished elaboration"
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
elaborate' (m, WeakTermPiElim (_, WeakTermZeta x) es) = do
  sub <- gets substEnv
  case Map.lookup x sub of
    Nothing ->
      throwError' $
      T.pack (showMeta m) <>
      ":error: couldn't instantiate the hole since no constraints are given on it"
    Just (_, WeakTermPiIntro xts e)
      | length xts == length es -> do
        let xs = map fst xts
        e' <- elaborate' $ substWeakTermPlus (zip xs es) e
        return e'
    Just _ -> throwError' "insane zeta"
elaborate' (m, WeakTermPiElim e es) = do
  e' <- elaborate' e
  es' <- mapM elaborate' es
  return (m, TermPiElim e' es')
elaborate' (m, WeakTermSigma xts) = do
  xts' <- mapM elaboratePlus xts
  z <- newNameWith "sigma"
  let zv = toTermUpsilon z
  k <- newNameWith "sig"
  -- Sigma [x1 : A1, ..., xn : An] = Pi (z : Type, _ : Pi [x1 : A1, ..., xn : An]. z). z
  let piType = (emptyMeta, TermPi xts' zv)
  return (m, TermPi [(z, univTerm), (k, piType)] zv)
elaborate' (m, WeakTermSigmaIntro t es) = do
  t' <- elaborate' t >>= reduceTermPlus
  es' <- mapM elaborate' es
  case t' of
    (_, TermPi [zu, kp@(k, (_, TermPi xts _))] _) -- i.e. Sigma xts
      | length xts == length es' -> do
        let xvs = map (toTermUpsilon . fst) xts
        let kv = toTermUpsilon k
        let bindArgsThen = \e -> (m, TermPiElim (m, TermPiIntro xts e) es')
        return $ bindArgsThen (m, TermPiIntro [zu, kp] (m, TermPiElim kv xvs))
    _ -> throwError' "the type of sigma-intro is wrong"
elaborate' (m, WeakTermSigmaElim t xts e1 e2) = do
  t' <- elaborate' t
  xts' <- mapM elaboratePlus xts
  e1' <- elaborate' e1
  e2' <- elaborate' e2
  -- sigma-elim t xts e1 e2 = e1 @ (t, lam xts. e2)
  return (m, TermPiElim e1' [t', (emptyMeta, TermPiIntro xts' e2')])
elaborate' (m, WeakTermIter (x, t) xts e) = do
  t' <- elaborate' t
  xts' <- mapM elaboratePlus xts
  e' <- elaborate' e
  return (m, TermIter (x, t') xts' e')
elaborate' (_, WeakTermZeta x) = do
  sub <- gets substEnv
  case Map.lookup x sub of
    Nothing -> throwError' $ "elaborate' i: remaining hole: " <> x
    Just e -> do
      e' <- elaborate' e
      return e'
elaborate' (m, WeakTermConst x) = do
  mi <- elaborateIsEnum x
  case mi of
    Nothing -> return (m, TermConst x)
    Just i -> return (m, TermEnumIntro (EnumValueIntU 64 i))
elaborate' (m, WeakTermConstDecl (x, t) e) = do
  t' <- elaborate' t
  e' <- elaborate' e
  return (m, TermConstDecl (x, t') e')
elaborate' (m, WeakTermInt t x) = do
  t' <- elaborate' t >>= reduceTermPlus
  case t' of
    (_, TermEnum (EnumTypeIntS size)) ->
      return (m, TermEnumIntro (EnumValueIntS size x))
    (_, TermEnum (EnumTypeIntU size)) ->
      return (m, TermEnumIntro (EnumValueIntU size x))
    _ -> do
      liftIO $ setSGR [SetConsoleIntensity BoldIntensity]
      liftIO $ putStrLn $ showMeta m ++ ":"
      liftIO $ setSGR [Reset]
      -- p $ showMeta m
      throwError' $
        "the type of `" <>
        T.pack (show x) <>
        "` should be an integer type, but is:\n" <> T.pack (show t')
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
          throwError' $
          T.pack (show x) <> " should be float, but is " <> floatType
    _ -> throwError' "elaborate.WeakTermFloat"
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
    _ -> throwError' "type error (enum elim)"
elaborate' (m, WeakTermArray dom k) = do
  dom' <- elaborate' dom
  return (m, TermArray dom' k)
elaborate' (m, WeakTermArrayIntro k es) = do
  es' <- mapM elaborate' es
  return (m, TermArrayIntro k es')
elaborate' (m, WeakTermArrayElim k xts e1 e2) = do
  e1' <- elaborate' e1
  xts' <- mapM elaboratePlus xts
  e2' <- elaborate' e2
  return (m, TermArrayElim k xts' e1' e2')
elaborate' (m, WeakTermStruct ts) = return (m, TermStruct ts)
elaborate' (m, WeakTermStructIntro eks) = do
  let (es, ks) = unzip eks
  es' <- mapM elaborate' es
  return (m, TermStructIntro $ zip es' ks)
elaborate' (m, WeakTermStructElim xts e1 e2) = do
  e1' <- elaborate' e1
  e2' <- elaborate' e2
  return (m, TermStructElim xts e1' e2')

elaboratePlus :: (a, WeakTermPlus) -> WithEnv (a, TermPlus)
elaboratePlus (x, t) = do
  t' <- elaborate' t
  return (x, t')

-- enum.n{i}   ~> Just i
-- enum.choice ~> Just 2 (assuming choice = {left, right})
-- otherwise   ~> Nothing
elaborateIsEnum :: Identifier -> WithEnv (Maybe Integer)
elaborateIsEnum x
  | Just i <- asEnumNatConstant x = return $ Just i
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
caseCheckEnumIdentifier (EnumTypeLabel x) ls = do
  es <- lookupEnumSet x
  caseCheckEnumIdentifier' (toInteger $ length es) ls
caseCheckEnumIdentifier (EnumTypeNat i) ls = do
  caseCheckEnumIdentifier' i ls
caseCheckEnumIdentifier (EnumTypeIntS _) ls =
  throwIfFalse $ CaseDefault `elem` ls
caseCheckEnumIdentifier (EnumTypeIntU _) ls =
  throwIfFalse $ CaseDefault `elem` ls

caseCheckEnumIdentifier' :: Integer -> [Case] -> WithEnv ()
caseCheckEnumIdentifier' i labelList = do
  let len = toInteger $ length (nub labelList)
  throwIfFalse $ i <= len || CaseDefault `elem` labelList

throwIfFalse :: Bool -> WithEnv ()
throwIfFalse b =
  if b
    then return ()
    else throwError' "non-exhaustive pattern"

lookupEnumSet :: Identifier -> WithEnv [Identifier]
lookupEnumSet name = do
  eenv <- gets enumEnv
  case Map.lookup name eenv of
    Nothing -> throwError' $ "no such enum defined: " <> name
    Just ls -> return ls

reduceSubstEnv :: WithEnv ()
reduceSubstEnv = do
  senv <- gets substEnv
  let senv' = Map.map reduceWeakTermPlus senv
  modify (\env -> env {substEnv = senv'})
