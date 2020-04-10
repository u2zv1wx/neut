{-# LANGUAGE OverloadedStrings #-}

module Elaborate
  ( elaborate
  ) where

import Control.Monad.State
import Data.List (find, nub)
import Data.Time
import Numeric

-- import Numeric.Half
import qualified Data.HashMap.Strict as Map
import qualified Data.IntMap.Strict as IntMap
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

-- import Data.Version (showVersion)
-- import Paths_neut (version)
-- Given a term `e` and its name `main`, this function
--   (1) traces `e` using `infer e`, collecting type constraints,
--   (2) updates weakTypeEnv for `main` by the result of `infer e`,
--   (3) analyze the constraints, solving easy ones,
--   (4) synthesize these analyzed constraints, solving as many solutions as possible,
--   (5) elaborate the given term using the result of synthesis.
-- The inference algorithm in this module is based on L. de Moura, J. Avigad,
-- S. Kong, and C. Roux. "Elaboration in Dependent Type Theory", arxiv,
-- https://arxiv.org/abs/1505.04324, 2015.
elaborate :: WeakStmt -> WithEnv TermPlus
elaborate stmt
  -- p "version:"
  -- p $ showVersion version -- ~> "0.1.0.0" が得られる。これをキャッシュディレクトリの構成に利用していく。
 = do
  reduceTermPlus <$> elaborateStmt stmt
  -- tmp <- reduceTermPlus <$> elaborateStmt stmt
  -- -- p "elaborated:"
  -- -- p $ T.unpack $ toText (weaken tmp)
  -- -- _ <- error "stop."
  -- -- p "tenv:"
  -- -- tenv <- gets typeEnv
  -- -- p' tenv
  -- return tmp

elaborateStmt :: WeakStmt -> WithEnv TermPlus
elaborateStmt (WeakStmtReturn e) = do
  (e', _) <- infer e
  analyze >> synthesize >> refine
  elaborate' e'
elaborateStmt (WeakStmtLet m (mx, x@(I (_, i)), t) e cont) = do
  (e', te) <- infer e
  t' <- inferType t
  insConstraintEnv te t'
  analyze >> synthesize >> refine >> cleanup
  e'' <- elaborate' e'
  t'' <- reduceTermPlus <$> elaborate' t'
  insTypeEnv x t''
  modify (\env -> env {cacheEnv = IntMap.insert i (Left e'') (cacheEnv env)})
  cont' <- elaborateStmt cont
  x' <- newNameWith x
  let c = (m, TermConst x)
  return (m, TermPiElim (m, TermPiIntro [(mx, x', t'')] cont') [c])
elaborateStmt (WeakStmtLetWT m (mx, x@(I (_, i)), t) e cont) = do
  t' <- inferType t
  analyze >> synthesize >> refine >> cleanup
  e' <- elaborate' e -- `e` is supposed to be well-typed
  t'' <- reduceTermPlus <$> elaborate' t'
  insTypeEnv x t''
  modify (\env -> env {cacheEnv = IntMap.insert i (Left e') (cacheEnv env)})
  cont' <- elaborateStmt cont
  x' <- newNameWith x
  let c = (m, TermConst x)
  return (m, TermPiElim (m, TermPiIntro [(mx, x', t'')] cont') [c])
elaborateStmt (WeakStmtVerify m e cont) = do
  (e', _) <- infer e
  e'' <- elaborate' e'
  start <- liftIO $ getCurrentTime
  _ <- normalize e''
  stop <- liftIO $ getCurrentTime
  let sec = realToFrac $ diffUTCTime stop start :: Float
  note m $ "verification succeeded (" <> T.pack (showFloat' sec) <> " seconds)"
  elaborateStmt cont
elaborateStmt (WeakStmtImplicit m x@(I (_, i)) idxList cont) = do
  t <- lookupTypeEnv' m x
  case t of
    (_, TermPi _ xts _) -> do
      case find (\idx -> idx < 0 || length xts <= idx) idxList of
        Nothing -> do
          ienv <- gets impEnv
          modify (\env -> env {impEnv = IntMap.insertWith (++) i idxList ienv})
          elaborateStmt cont
        Just idx -> do
          raiseError m $
            "the specified index `" <>
            T.pack (show idx) <>
            "` is out of range of the domain of " <> asText x
    _ ->
      raiseError m $
      "the type of " <>
      asText x <> " is supposed to be a Pi-type, but is:\n" <> toText (weaken t)
elaborateStmt (WeakStmtConstDecl _ (_, x, t) cont) = do
  t' <- inferType t
  analyze >> synthesize >> refine >> cleanup
  t'' <- reduceTermPlus <$> elaborate' t'
  insTypeEnv x t''
  elaborateStmt cont

showFloat' :: Float -> String
showFloat' x = showFFloat Nothing x ""

refine :: WithEnv ()
refine =
  modify (\env -> env {substEnv = IntMap.map reduceWeakTermPlus (substEnv env)})

cleanup :: WithEnv ()
cleanup = do
  modify (\env -> env {constraintEnv = []})
  modify (\env -> env {weakTypeEnv = IntMap.empty})
  modify (\env -> env {zetaEnv = IntMap.empty})

-- This function translates a well-typed term into an untyped term in a
-- reduction-preserving way. Here, we translate types into units (nullary product).
-- This doesn't cause any problem since types doesn't have any beta-reduction.
elaborate' :: WeakTermPlus -> WithEnv TermPlus
elaborate' (m, WeakTermTau) = return (m, TermTau)
elaborate' (m, WeakTermUpsilon x) = do
  cenv <- gets cacheEnv
  if IntMap.member (asInt x) cenv
    then return (m, TermConst x)
    else return (m, TermUpsilon x)
elaborate' (m, WeakTermPi mName xts t) = do
  xts' <- mapM elaboratePlus xts
  t' <- elaborate' t
  return (m, TermPi mName xts' t')
elaborate' (m, WeakTermPiIntro xts e) = do
  e' <- elaborate' e
  xts' <- mapM elaboratePlus xts
  return (m, TermPiIntro xts' e')
-- elaborate' (m, WeakTermPiIntroNoReduce xts e) = do
--   e' <- elaborate' e
--   xts' <- mapM elaboratePlus xts
--   return (m, TermPiIntroNoReduce xts' e')
elaborate' (m, WeakTermPiIntroPlus ind (name, is, args1, args2) xts e) = do
  args1' <- mapM elaboratePlus args1
  args2' <- mapM elaboratePlus args2
  e' <- elaborate' e
  xts' <- mapM elaboratePlus xts
  return (m, TermPiIntroPlus ind (name, is, args1', args2') xts' e')
elaborate' (m, WeakTermPiElim (mh, WeakTermZeta (I (_, x))) es) = do
  sub <- gets substEnv
  case IntMap.lookup x sub of
    Nothing -> raiseError mh $ "couldn't instantiate the hole here"
    Just (_, WeakTermPiIntro xts e)
      | length xts == length es -> do
        let xs = map (\(_, y, _) -> y) xts
        elaborate' $ substWeakTermPlus (zip xs es) e
    Just e -> elaborate' $ reduceWeakTermPlus (m, WeakTermPiElim e es)
elaborate' (m, WeakTermPiElim e es) = do
  e' <- elaborate' e
  es' <- mapM elaborate' es
  return (m, TermPiElim e' es')
elaborate' (m, WeakTermIter (mx, x, t) xts e) = do
  t' <- elaborate' t
  xts' <- mapM elaboratePlus xts
  e' <- elaborate' e
  return (m, TermIter (mx, x, t') xts' e')
elaborate' (m, WeakTermZeta _) =
  raiseCritical
    m
    "every meta-variable must be of the form (?M e1 ... en) where n >= 0, but found the meta-variable here that doesn't fit this pattern"
elaborate' (m, WeakTermConst x) = return (m, TermConst x)
elaborate' (m, WeakTermInt t x) = do
  t' <- reduceTermPlus <$> elaborate' t
  case t' of
    (_, TermEnum (EnumTypeIntS size))
      | (-1) * (2 ^ (size - 1)) <= x
      , x < 2 ^ size -> return (m, TermEnumIntro (EnumValueIntS size x))
      | otherwise ->
        raiseError m $
        "the signed integer " <>
        T.pack (show x) <>
        " is inferred to be of type i" <>
        T.pack (show size) <> ", but is out of range of i" <> T.pack (show size)
    (_, TermEnum (EnumTypeIntU size))
      | 0 <= x
      , x < 2 ^ size -> return (m, TermEnumIntro (EnumValueIntU size x))
      | otherwise ->
        raiseError m $
        "the unsigned integer " <>
        T.pack (show x) <>
        " is inferred to be of type u" <>
        T.pack (show size) <> ", but is out of range of u" <> T.pack (show size)
    _ ->
      raiseError m $
      "the term `" <>
      T.pack (show x) <>
      "` is an integer, but its type is: " <> toText (weaken t')
elaborate' (m, WeakTermFloat t x) = do
  t' <- reduceTermPlus <$> elaborate' t
  case t' of
    (_, TermConst (I (floatType, i)))
      | Just (LowTypeFloat size) <- asLowTypeMaybe floatType -> do
        return (m, TermFloat (size, i) x)
    _ ->
      raiseError m $
      "the term `" <>
      T.pack (show x) <>
      "` is a float, but its type is:\n" <> toText (weaken t')
elaborate' (m, WeakTermEnum k) = return (m, TermEnum k)
elaborate' (m, WeakTermEnumIntro x) = return (m, TermEnumIntro x)
elaborate' (m, WeakTermEnumElim (e, t) les) = do
  e' <- elaborate' e
  let (ls, es) = unzip les
  ls' <- mapM elaborateWeakCase ls
  es' <- mapM elaborate' es
  t' <- reduceTermPlus <$> elaborate' t
  case t' of
    (_, TermEnum x) -> do
      caseCheckEnumIdentifier m x $ map snd ls'
      return (m, TermEnumElim (e', t') (zip ls' es'))
    _ ->
      raiseError m $
      "the type of `" <>
      toText (weaken e') <>
      "` must be an enum type, but is:\n" <> toText (weaken t')
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
elaborate' (m, WeakTermCase indName e cxtes) = do
  e' <- elaborate' e
  cxtes' <-
    forM cxtes $ \((c, xts), body) -> do
      xts' <- mapM elaboratePlus xts
      body' <- elaborate' body
      return ((c, xts'), body')
  eenv <- gets enumEnv
  case cxtes' of
    [] -> do
      case Map.lookup indName eenv of
        Nothing -> raiseError m $ "no such inductive type defined: " <> indName
        Just [] -> return (m, TermCase indName e' cxtes')
        Just _ ->
          raiseError m $
          "the inductive type `" <> indName <> "` is not a bottom-type"
    _ -> do
      case Map.lookup indName eenv of
        Nothing -> raiseError m $ "no such inductive type defined: " <> indName
        Just bis -> do
          let bs' = map (asText . snd . fst . fst) cxtes
          let isLinear = linearCheck bs'
          let isExhaustive = length bis == length bs'
          case (isLinear, isExhaustive) of
            (False, _) -> raiseError m $ "found a non-linear pattern"
            (_, False) -> raiseError m $ "found a non-exhaustive pattern"
            (True, True) -> return (m, TermCase indName e' cxtes')
elaborate' (m, WeakTermQuestion e t) = do
  e' <- elaborate' e
  whenCheck $ do
    t' <- elaborate' t
    case getArgLen t' of
      Nothing -> do
        note m $ toText (weaken t')
      Just len -> do
        (is, e'') <- getImpInfo e'
        let form = toText (weaken e'') : showFormArgs 0 is [0 .. len - 1]
        let formStr = inParen $ showItems form
        note m $ toText (weaken t') <> "\n-\n" <> formStr
  return e'
elaborate' (_, WeakTermErase _ e) = elaborate' e

getImpInfo :: TermPlus -> WithEnv ([Int], TermPlus)
getImpInfo e@(m, TermConst x)
  | not (metaIsExplicit m) = do
    ienv <- gets impEnv
    case IntMap.lookup (asInt x) ienv of
      Just is -> return (is, e)
      Nothing -> return ([], e)
  | otherwise = return ([], (m, TermConst $ I ("@" <> asText x, asInt x)))
getImpInfo e = return ([], e)

getArgLen :: TermPlus -> Maybe Int
getArgLen (_, TermPi _ xts _) = return $ length xts
getArgLen _ = Nothing

showFormArgs :: Int -> [Int] -> [Int] -> [T.Text]
showFormArgs _ _ [] = []
showFormArgs k impList [i]
  | i `elem` impList = ["*"]
  | otherwise = ["#" <> T.pack (show k)]
showFormArgs k impList (i:is)
  | i `elem` impList = "*" : showFormArgs k impList is
  | otherwise = "#" <> T.pack (show k) : showFormArgs (k + 1) impList is

elaborateWeakCase :: WeakCasePlus -> WithEnv CasePlus
elaborateWeakCase (m, WeakCaseInt t x) = do
  t' <- reduceTermPlus <$> elaborate' t
  case t' of
    (_, TermEnum (EnumTypeIntS size)) ->
      return (m, CaseValue (EnumValueIntS size x))
    (_, TermEnum (EnumTypeIntU size)) ->
      return (m, CaseValue (EnumValueIntU size x))
    (_, TermEnum (EnumTypeLabel "bool")) ->
      return (m, CaseValue (EnumValueIntS 1 x))
    _ -> do
      raiseError m $
        "the type of `" <>
        T.pack (show x) <>
        "` must be an integer type, but is: " <> toText (weaken t')
elaborateWeakCase (m, WeakCaseLabel l) =
  return (m, CaseValue $ EnumValueLabel l)
elaborateWeakCase (m, WeakCaseIntS t a) =
  return (m, CaseValue $ EnumValueIntS t a)
elaborateWeakCase (m, WeakCaseIntU t a) =
  return (m, CaseValue $ EnumValueIntU t a)
elaborateWeakCase (m, WeakCaseDefault) = return (m, CaseDefault)

elaboratePlus :: (Meta, a, WeakTermPlus) -> WithEnv (Meta, a, TermPlus)
elaboratePlus (m, x, t) = do
  t' <- elaborate' t
  return (m, x, t')

caseCheckEnumIdentifier :: Meta -> EnumType -> [Case] -> WithEnv ()
caseCheckEnumIdentifier m (EnumTypeLabel x) ls = do
  es <- lookupEnumSet m x
  caseCheckEnumIdentifier' m (length es) ls
caseCheckEnumIdentifier m (EnumTypeIntS _) ls =
  throwIfFalse m $ CaseDefault `elem` ls
caseCheckEnumIdentifier m (EnumTypeIntU _) ls =
  throwIfFalse m $ CaseDefault `elem` ls

caseCheckEnumIdentifier' :: Meta -> Int -> [Case] -> WithEnv ()
caseCheckEnumIdentifier' m i labelList = do
  let len = length (nub labelList)
  throwIfFalse m $ i <= len || CaseDefault `elem` labelList

throwIfFalse :: Meta -> Bool -> WithEnv ()
throwIfFalse m b =
  if b
    then return ()
    else raiseError m "non-exhaustive pattern"

lookupEnumSet :: Meta -> T.Text -> WithEnv [T.Text]
lookupEnumSet m name = do
  eenv <- gets enumEnv
  case Map.lookup name eenv of
    Nothing -> raiseError m $ "no such enum defined: " <> name
    Just xis -> return $ map fst xis
