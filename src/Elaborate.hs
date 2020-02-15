{-# LANGUAGE OverloadedStrings #-}

module Elaborate
  ( elaborate
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.List (nub)
import Data.Maybe (catMaybes, fromMaybe)
import Debug.Trace
import Numeric.Half
import System.Console.ANSI

import qualified Data.HashMap.Strict as Map
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Set as S
import qualified Data.Text as T

import Data.Basic
import Data.Constraint
import Data.Env
import Data.Term
import Data.WeakTerm
import Elaborate.Analyze
import Elaborate.Infer
import Elaborate.Synthesize
import Reduce.Term
import Reduce.WeakTerm

import qualified Data.UnionFind as UF

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
elaborate stmt = elaborateStmt stmt >>= reduceTermPlus

elaborateStmt :: WeakStmt -> WithEnv TermPlus
elaborateStmt (WeakStmtReturn e) = do
  (e', _, _) <- infer e
  analyze >> synthesize >> refine
  -- p "univ-level"
  -- _ <- error "stop"
  checkUnivSanity
  -- p "done"
  elaborate' e' >>= reduceTermPlus
elaborateStmt (WeakStmtLet m (mx, x, t) e cont) = do
  (e', te, mle) <- infer e
  (t', mlt) <- inferType t
  -- p $ "==== " ++ T.unpack x ++ " ===="
  -- p $ T.unpack (toText e')
  -- p $ T.unpack (toText t')
  insConstraintEnv te t'
  insLevelEQ mle mlt
  modify (\env -> env {substEnv = Map.insert x e' (substEnv env)})
  -- Kantian type-inference
  analyze >> synthesize >> refine >> cleanup
  -- elaborateStmt the related terms
  e'' <- elaborate' e' >>= reduceTermPlus
  t'' <- elaborate' t' >>= reduceTermPlus
  insTypeEnv x t'' mlt
  -- outputGraph
  cont' <- elaborateStmt cont
  return (m, TermPiElim (m, TermPiIntro [(mx, x, t'')] cont') [e''])
elaborateStmt (WeakStmtConstDecl m (mx, x, t) cont)
  -- p $ "==== " ++ T.unpack x ++ " ===="
  -- p $ T.unpack (toText t)
 = do
  (t', mlt) <- inferType t
  analyze >> synthesize >> refine >> cleanup
  t'' <- elaborate' t' >>= reduceTermPlus
  insTypeEnv x t'' mlt
  cont' <- elaborateStmt cont
  return (m, TermConstDecl (mx, x, t'') cont')

refine :: WithEnv ()
refine =
  modify (\env -> env {substEnv = Map.map reduceWeakTermPlus (substEnv env)})

cleanup :: WithEnv ()
cleanup = do
  modify (\env -> env {constraintEnv = []})
  modify (\env -> env {weakTypeEnv = Map.empty})
  modify (\env -> env {zetaEnv = Map.empty})

type LevelEdge = ((Meta, UnivLevel), (Integer, (Meta, UnivLevel)))

-- equalityを処理してからedgeを構成していく
quotient ::
     [(UnivLevel, UnivLevel)]
  -> UnivInstEnv
  -> [LevelConstraint]
  -> UF.UnionFind [LevelEdge]
quotient [] uienv g = concat <$> mapM (quotient' uienv) g
quotient ((l1, l2):lls) uienv g = do
  UF.union l1 l2
  quotient lls uienv g

quotient' :: UnivInstEnv -> LevelConstraint -> UF.UnionFind [LevelEdge]
quotient' uienv (UnivLevelPlus (m1, l1), (w, UnivLevelPlus (m2, l2))) = do
  let domList = inst uienv l1
  let codList = inst uienv l2
  forM (cartesianProduct domList codList) $ \(dom, cod) -> do
    dom' <- UF.find dom
    cod' <- UF.find cod
    return ((m1, dom'), (w, (m2, cod')))

cartesianProduct :: [a] -> [b] -> [(a, b)]
cartesianProduct xs ys = do
  x <- xs
  y <- ys
  return (x, y)

inst :: UnivInstEnv -> UnivLevel -> [UnivLevel]
inst uienv l =
  case IntMap.lookup l uienv of
    Nothing -> [l]
    Just ls -> S.toList ls

checkUnivSanity :: WithEnv ()
checkUnivSanity = do
  g <- gets levelEnv
  eenv <- gets equalityEnv
  uienv <- gets univInstEnv
  let g' = nub $ UF.run $ quotient eenv uienv g
  -- p' $ map (\(a, (w, b)) -> (UnivLevelPlus a, (w, UnivLevelPlus b))) g'
  let nodeList = nub $ concatMap (\(n1, _) -> [n1]) g'
  let g'' = toGraph g'
  -- g'' <- return $ toGraph g'
  -- let s = sum $ map (\(_, xs) -> length xs) $ IntMap.toList g''
  -- p $ "constructed graph. size = " ++ show s
  -- p $ "nodes: " ++ show (length nodeList)
  -- forGraphviz $ IntMap.toList g''
  -- g2 <- return $ toGraph $ nub g'
  -- let s2 = sum $ map (\(_, xs) -> length xs) $ IntMap.toList g2
  -- p $ "constructed graph. size = " ++ show s2
  ensureDAG' g'' IntMap.empty nodeList

-- outputGraph :: WithEnv ()
-- outputGraph = do
--   g <- gets levelEnv
--   eenv <- gets equalityEnv
--   uienv <- gets univInstEnv
--   let g' = nub $ UF.run $ quotient eenv uienv g
--   let g'' = toGraph g'
--   -- p' g''
--   forGraphviz $ IntMap.toList g''
-- forGraphviz :: [(IntMap.Key, [(Integer, (a, Int))])] -> WithEnv ()
-- forGraphviz wxs
--   -- p "digraph {"
--  = do
--   forGraphviz' wxs
--   -- p "}"
-- forGraphviz' :: [(IntMap.Key, [(Integer, (a, Int))])] -> WithEnv ()
-- forGraphviz' [] = return ()
-- forGraphviz' ((i1, ws):xs) = do
--   forGraphviz'' i1 ws
--   forGraphviz' xs
-- forGraphviz'' :: IntMap.Key -> [(Integer, (a, Int))] -> WithEnv ()
-- forGraphviz'' _ [] = return ()
-- forGraphviz'' i ((w, (_, j)):wjs) = do
--   if w <= 0
--     then p $ "  " ++ show i ++ " <= " ++ show j
--     else p $ "  " ++ show i ++ " < " ++ show j
--   -- if w <= 0
--   --   then p $ "  " ++ show i ++ " -> " ++ show j ++ ";"
--   --   else p $ "  " ++ show i ++ " -> " ++ show j ++ "[color=red];"
--   forGraphviz'' i wjs
type LevelGraph = IntMap.IntMap [(Integer, (Meta, UnivLevel))]

toGraph :: [LevelEdge] -> LevelGraph
toGraph [] = IntMap.empty
toGraph (((_, l1), v@(_, (_, _))):kvs) =
  IntMap.insertWith (++) l1 [v] $ toGraph kvs

ensureDAG' :: LevelGraph -> NodeInfo -> [(Meta, UnivLevel)] -> WithEnv ()
ensureDAG' _ _ [] = return ()
ensureDAG' g nodeInfo (v:vs) = do
  let l = snd v
  case IntMap.lookup l nodeInfo of
    Just NodeStateFinish -> ensureDAG' g nodeInfo vs
    Just NodeStateActive -> error "invalid argument"
    Nothing ->
      case dfs g v [(0, v)] nodeInfo of
        Right finishedList -> do
          let info = IntMap.fromList $ zip finishedList (repeat NodeStateFinish)
          ensureDAG' g (IntMap.union info nodeInfo) vs
          -- ensureDAG' g (IntMap.insert l NodeStateFinish nodeInfo) vs
        Left closedPath ->
          throwError' $
          "found cyclic univ level:\n" <>
          T.pack (show $ map (\(x, y) -> (x, UnivLevelPlus y)) closedPath)

-- toGraph ((UnivLevelPlus (_, l), v):kvs) = do
--   Map.insertWith (\v1 v2 -> v1 ++ v2) l [v] $ toGraph kvs
type UnivPath = [(Integer, (Meta, UnivLevel))]

type NodeInfo = IntMap.IntMap NodeState

data NodeState
  = NodeStateActive
  | NodeStateFinish

dfs ::
     LevelGraph
  -> (Meta, UnivLevel)
  -> UnivPath
  -> NodeInfo
  -> Either UnivPath [UnivLevel]
dfs g (_, l) path visitInfo = do
  let mvs = fromMaybe [] $ IntMap.lookup l g
  foo <-
    sequence $
    (flip map) mvs $ \wv'@(_, v')
      -- let path' = path ++ [wv']
     -> do
      let path' = wv' : path
      let l' = snd v'
      case IntMap.lookup l' visitInfo of
        Just NodeStateActive -> do
          let closedPath = dropWhile (\(_, ml'') -> snd ml'' /= l') path'
          if weightOf closedPath > 0
            then Left closedPath
            else return []
        Just NodeStateFinish -> return []
        Nothing -> do
          dfs g v' path' (IntMap.insert l NodeStateActive visitInfo)
  --         return $ l' : ls
  return $ l : concat foo

weightOf :: UnivPath -> Integer
weightOf path = sum $ map fst $ tail path

-- This function translates a well-typed term into an untyped term in a
-- reduction-preserving way. Here, we translate types into units (nullary product).
-- This doesn't cause any problem since types doesn't have any beta-reduction.
elaborate' :: WeakTermPlus -> WithEnv TermPlus
elaborate' (m, WeakTermTau l) = do
  return (m, TermTau l)
elaborate' (m, WeakTermUpsilon x) = do
  return (m, TermUpsilon x)
elaborate' (m, WeakTermPi mls xts t) = do
  xts' <- mapM elaboratePlus xts
  t' <- elaborate' t
  return (m, TermPi mls xts' t')
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
        let xs = map (\(_, y, _) -> y) xts
        e' <- elaborate' $ substWeakTermPlus (zip xs es) e
        return e'
    Just _ -> throwError' "insane zeta"
elaborate' (m, WeakTermPiElim e es) = do
  e' <- elaborate' e
  es' <- mapM elaborate' es
  return (m, TermPiElim e' es')
elaborate' (m, WeakTermSigma xts) = do
  xts' <- mapM elaboratePlus xts
  return (m, TermSigma xts')
  -- z <- newNameWith "sigma"
  -- let zv = toTermUpsilon z
  -- k <- newNameWith "sig"
  -- -- Sigma [x1 : A1, ..., xn : An] = Pi (z : Type, _ : Pi [x1 : A1, ..., xn : An]. z). z
  -- let piType = (emptyMeta, TermPi xts' zv)
  -- -- fixme: level info of sigma is required
  -- let univTerm = undefined
  -- return (m, TermPi [(emptyMeta, z, univTerm), (emptyMeta, k, piType)] zv)
elaborate' (m, WeakTermSigmaIntro t es) = do
  t' <- elaborate' t
  es' <- mapM elaborate' es
  return (m, TermSigmaIntro t' es')
  -- case t' of
  --   (_, TermPi [zu, kp@(_, k, (_, TermPi xts _))] _) -- i.e. Sigma xts
  --     | length xts == length es' -> do
  --       let xvs = map (\(_, x, _) -> toTermUpsilon x) xts
  --       let kv = toTermUpsilon k
  --       let bindArgsThen = \e -> (m, TermPiElim (m, TermPiIntro xts e) es')
  --       return $ bindArgsThen (m, TermPiIntro [zu, kp] (m, TermPiElim kv xvs))
  --   _ -> throwError' "the type of sigma-intro is wrong"
elaborate' (m, WeakTermSigmaElim t xts e1 e2) = do
  t' <- elaborate' t
  xts' <- mapM elaboratePlus xts
  e1' <- elaborate' e1
  e2' <- elaborate' e2
  return (m, TermSigmaElim t' xts' e1' e2')
  -- sigma-elim t xts e1 e2 = e1 @ (t, lam xts. e2)
  -- return (m, TermPiElim e1' [t', (emptyMeta, TermPiIntro xts' e2')])
elaborate' (m, WeakTermIter (mx, x, t) xts e) = do
  t' <- elaborate' t
  xts' <- mapM elaboratePlus xts
  e' <- elaborate' e
  return (m, TermIter (mx, x, t') xts' e')
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
elaborate' (m, WeakTermConstDecl (mx, x, t) e) = do
  t' <- elaborate' t
  e' <- elaborate' e
  return (m, TermConstDecl (mx, x, t') e')
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
  let (ls, es) = unzip les
  ls' <- mapM elaborateWeakCase ls
  es' <- mapM elaborate' es
  -- les' <- forM les elaboratePlus
  t' <- elaborate' t >>= reduceTermPlus
  case t' of
    (_, TermEnum x) -> do
      caseCheckEnumIdentifier x ls'
      return (m, TermEnumElim (e', t') (zip ls' es'))
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

elaborateWeakCase :: WeakCase -> WithEnv Case
elaborateWeakCase (WeakCaseInt t x) = do
  t' <- elaborate' t >>= reduceTermPlus
  case t' of
    (_, TermEnum (EnumTypeIntS size)) ->
      return $ CaseValue (EnumValueIntS size x)
    (_, TermEnum (EnumTypeIntU size)) ->
      return $ CaseValue (EnumValueIntU size x)
    _ -> do
      let m = fst t
      liftIO $ setSGR [SetConsoleIntensity BoldIntensity]
      liftIO $ putStrLn $ showMeta m ++ ":"
      liftIO $ setSGR [Reset]
      p $ showMeta m
      throwError' $
        "the type of `" <>
        T.pack (show x) <>
        "` should be an integer type, but is:\n" <> T.pack (show t')
elaborateWeakCase (WeakCaseLabel l) = return $ CaseValue $ EnumValueLabel l
elaborateWeakCase (WeakCaseIntS t a) = return $ CaseValue $ EnumValueIntS t a
elaborateWeakCase (WeakCaseIntU t a) = return $ CaseValue $ EnumValueIntU t a
elaborateWeakCase (WeakCaseNat t a) = return $ CaseValue $ EnumValueNat t a
elaborateWeakCase WeakCaseDefault = return $ CaseDefault

elaboratePlus :: (Meta, a, WeakTermPlus) -> WithEnv (Meta, a, TermPlus)
elaboratePlus (m, x, t) = do
  t' <- elaborate' t
  return (m, x, t')

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
    Just xis -> return $ map fst xis
