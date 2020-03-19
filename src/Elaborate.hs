{-# LANGUAGE OverloadedStrings #-}

module Elaborate
  ( elaborate
  ) where

import Control.Monad.State
import Data.List (nub)
import Data.Maybe (fromMaybe)
import Numeric.Half

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
elaborate stmt = do
  e <- elaborateStmt stmt
  e' <- reduceTermPlus e
  return e'
  -- _ <- error "well-typed"
  -- return e

elaborateStmt :: WeakStmt -> WithEnv TermPlus
elaborateStmt (WeakStmtReturn e) = do
  (e', _, _) <- infer e
  analyze >> synthesize >> refine
  checkUnivSanity
  elaborate' e' >>= reduceTermPlus
elaborateStmt (WeakStmtLet m (mx, x@(I (_, i)), t) e cont) = do
  (e', te, mle) <- infer e
  (t', mlt) <- inferType t
  insConstraintEnv te t'
  insLevelEQ mle mlt
  -- Kantian type-inference ;)
  analyze >> synthesize >> refine >> cleanup
  e'' <- elaborate' e' >>= reduceTermPlus
  t'' <- elaborate' t' >>= reduceTermPlus
  insTypeEnv x t'' mlt
  modify (\env -> env {substEnv = IntMap.insert i (weaken e'') (substEnv env)})
  -- liftIO $ TIO.putStrLn $ toText $ weaken t''
  cont' <- elaborateStmt cont
  return (m, TermPiElim (m, TermPiIntro [(mx, x, t'')] cont') [e''])
elaborateStmt (WeakStmtLetWT m (mx, x@(I (_, i)), t) e cont) = do
  (t', mlt) <- inferType t
  analyze >> synthesize >> refine >> cleanup
  e' <- elaborate' e -- `e` is supposed to be well-typed
  t'' <- elaborate' t' >>= reduceTermPlus
  insTypeEnv x t'' mlt
  modify (\env -> env {substEnv = IntMap.insert i (weaken e') (substEnv env)})
  cont' <- elaborateStmt cont
  return (m, TermPiElim (m, TermPiIntro [(mx, x, t'')] cont') [e'])
elaborateStmt (WeakStmtLetSigma m xts e cont) = do
  (e', t1, mlSigma) <- infer e
  xtls <- inferSigma [] xts
  let (xts', mlSigArgList) = unzip xtls
  insConstraintEnv t1 (fst e', WeakTermSigma xts')
  forM_ mlSigArgList $ \mlSigArg -> insLevelLE mlSigArg mlSigma
  analyze >> synthesize >> refine >> cleanup
  e'' <- elaborate' e' >>= reduceTermPlus
  xts'' <- mapM elaboratePlus xts'
  forM_ (zip xts'' mlSigArgList) $ \((_, x, tx), l) -> insTypeEnv x tx l
  cont' <- elaborateStmt cont
  return
    (m, TermSigmaElim (m, TermEnumIntro $ EnumValueLabel "top") xts'' e'' cont')
elaborateStmt (WeakStmtImplicit m x@(I (_, i)) idx cont) = do
  t <- lookupTypeEnv' x
  case t of
    (_, TermPi _ xts _) -> do
      if 0 <= idx && idx < length xts
        then do
          ienv <- gets impEnv
          modify (\env -> env {impEnv = IntMap.insertWith (++) i [idx] ienv})
          elaborateStmt cont
        else raiseError m $
             "the specified index `" <>
             T.pack (show idx) <>
             "` is out of range of the domain of " <> asText x
    _ ->
      raiseError m $
      "the type of " <>
      asText x <> " is supposed to be a Pi-type, but is:\n" <> toText (weaken t)
elaborateStmt (WeakStmtLetInductiveIntro m (bi, ai) (mx, x@(I (_, i)), t) xts yts atsbts app cont) = do
  (t', mlt) <- inferType t
  analyze >> synthesize >> refine >> cleanup
  -- the "elaborate' e" part in LetWT
  app' <- elaborate' app
  atsbts' <- mapM elaboratePlus atsbts
  -- collect free-var info
  -- ch <- chainTermPlus (m, TermPiIntro atsbts' app')
  -- let s = map (\(mz, z, tz) -> (z, ((mz, TermUpsilon z), tz))) ch
  -- let ys = map (\(_, y, _) -> y) yts
  -- このidxはたぶんenvのほうに登録するべき
  -- let idx = findIndices (\(z, _) -> z `elem` ys) s
  xtsyts' <- mapM elaboratePlus $ xts ++ yts
  let lam =
        ( m
        , TermPiIntroNoReduce
            xtsyts'
            (m, TermPiIntroPlus ai (bi, xtsyts') atsbts' app'))
  -- let lam =
  --       (m, TermPiIntro xtsyts' (m, TermPiIntroPlus bi ai False s atsbts' app'))
  -- the "elaboreta' e" part ends here
  t'' <- elaborate' t' >>= reduceTermPlus
  insTypeEnv x t'' mlt
  modify (\env -> env {substEnv = IntMap.insert i (weaken lam) (substEnv env)})
  cont' <- elaborateStmt cont
  return (m, TermPiElim (m, TermPiIntro [(mx, x, t'')] cont') [lam])
elaborateStmt (WeakStmtConstDecl m (mx, x, t) cont) = do
  (t', mlt) <- inferType t
  analyze >> synthesize >> refine >> cleanup
  t'' <- elaborate' t' >>= reduceTermPlus
  -- i <- lookupConstNum' x
  insTypeEnv x t'' mlt
  -- insTypeEnv (I (x, i)) t'' mlt
  cont' <- elaborateStmt cont
  return (m, TermConstDecl (mx, x, t'') cont')
  -- return (m, TermConstDecl (mx, I (x, i), t'') cont')

-- fixme: 余計なreduceをしているので修正すること
refine :: WithEnv ()
refine =
  modify (\env -> env {substEnv = IntMap.map reduceWeakTermPlus (substEnv env)})

cleanup :: WithEnv ()
cleanup = do
  modify (\env -> env {constraintEnv = []})
  modify (\env -> env {weakTypeEnv = IntMap.empty})
  modify (\env -> env {zetaEnv = IntMap.empty})

type LevelEdge = ((Meta, UnivLevel), (Integer, (Meta, UnivLevel)))

-- equalityを処理してからedgeを構成していく
quotient ::
     [(UnivLevel, UnivLevel)]
  -> UnivInstEnv
  -> [LevelConstraint]
  -> UF.UnionFind (S.Set (Meta, UnivLevel), S.Set LevelEdge)
quotient [] uienv g = quotient' uienv g
quotient ((l1, l2):lls) uienv g = do
  UF.union l1 l2
  quotient lls uienv g

quotient' ::
     UnivInstEnv
  -> [LevelConstraint]
  -> UF.UnionFind (S.Set (Meta, UnivLevel), S.Set LevelEdge)
quotient' _ [] = return (S.empty, S.empty)
quotient' uienv ((UnivLevelPlus (m1, l1), (w, UnivLevelPlus (m2, l2))):ss) = do
  (vs, g) <- quotient' uienv ss
  let domList = inst uienv l1
  let codList = inst uienv l2
  return
    ( S.insert (m1, l1) vs
    , quotient'' g m1 w m2 $ cartesianProduct domList codList)

quotient'' ::
     S.Set LevelEdge
  -> Meta
  -> Integer
  -> Meta
  -> [(UnivLevel, UnivLevel)]
  -> S.Set LevelEdge
quotient'' g _ _ _ [] = g
quotient'' g m1 w m2 ((dom, cod):rest) =
  S.insert ((m1, dom), (w, (m2, cod))) $ quotient'' g m1 w m2 rest

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
  let (vs, g') = UF.run $ quotient eenv uienv g
  let g'' = toGraph $ S.toList g'
  ensureDAG g'' IntMap.empty (S.toList vs)

type LevelGraph = IntMap.IntMap [(Integer, (Meta, UnivLevel))]

toGraph :: [LevelEdge] -> LevelGraph
toGraph [] = IntMap.empty
toGraph (((_, l1), v@(_, (_, _))):kvs) =
  IntMap.insertWith (++) l1 [v] $ toGraph kvs

ensureDAG :: LevelGraph -> NodeInfo -> [(Meta, UnivLevel)] -> WithEnv ()
ensureDAG _ _ [] = return ()
ensureDAG g nodeInfo (v:vs) = do
  let l = snd v
  case IntMap.lookup l nodeInfo of
    Just NodeStateFinish -> ensureDAG g nodeInfo vs
    Just NodeStateActive -> error "invalid argument"
    Nothing ->
      case dfs g v [(0, v)] nodeInfo of
        Right finishedList -> do
          let info = IntMap.fromList $ zip finishedList (repeat NodeStateFinish)
          ensureDAG g (IntMap.union info nodeInfo) vs
        Left closedPath -> do
          let (_, (m, _)) = head closedPath
          raiseError m $
            "found cyclic univ level:\n" <>
            T.pack
              (show $ map (\(x, y) -> (x, UnivLevelPlus y)) (reverse closedPath))

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
  lss <-
    sequence $
    (flip map) mvs $ \wv'@(_, v') -> do
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
  return $ l : concat lss

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
elaborate' (m, WeakTermPiPlus name mls xts t) = do
  xts' <- mapM elaboratePlus xts
  t' <- elaborate' t
  return (m, TermPiPlus name mls xts' t')
elaborate' (m, WeakTermPiIntro xts e) = do
  e' <- elaborate' e
  xts' <- mapM elaboratePlus xts
  return (m, TermPiIntro xts' e')
elaborate' (m, WeakTermPiIntroNoReduce xts e) = do
  e' <- elaborate' e
  xts' <- mapM elaboratePlus xts
  return (m, TermPiIntroNoReduce xts' e')
elaborate' (m, WeakTermPiIntroPlus ind (name, args) xts e) = do
  args' <- mapM elaboratePlus args
  -- let (zs, ees) = unzip s
  -- let (es1, es2) = unzip ees
  -- es1' <- mapM elaborate' es1
  -- es2' <- mapM elaborate' es2
  e' <- elaborate' e
  xts' <- mapM elaboratePlus xts
  -- return
  --   (m, TermPiIntroPlus name indName False (zip zs (zip es1' es2')) xts' e')
  return (m, TermPiIntroPlus ind (name, args') xts' e')
elaborate' (m, WeakTermPiElim (_, WeakTermZeta h@(I (_, x))) es) = do
  sub <- gets substEnv
  case IntMap.lookup x sub of
    Nothing ->
      raiseError m $
      "couldn't instantiate the hole since no constraints are given on it"
    Just (_, WeakTermPiIntro xts e)
      | length xts == length es -> do
        let xs = map (\(_, y, _) -> y) xts
        e' <- elaborate' $ substWeakTermPlus (zip xs es) e
        return e'
    Just _ ->
      raiseCritical m $
      "the hole " <>
      asText' h <> " is not registered in the substitution environment"
elaborate' (m, WeakTermPiElim e es) = do
  e' <- elaborate' e
  es' <- mapM elaborate' es
  return (m, TermPiElim e' es')
elaborate' (m, WeakTermSigma xts) = do
  xts' <- mapM elaboratePlus xts
  return (m, TermSigma xts')
elaborate' (m, WeakTermSigmaIntro t es) = do
  t' <- elaborate' t
  es' <- mapM elaborate' es
  return (m, TermSigmaIntro t' es')
elaborate' (m, WeakTermSigmaElim t xts e1 e2) = do
  t' <- elaborate' t
  xts' <- mapM elaboratePlus xts
  e1' <- elaborate' e1
  e2' <- elaborate' e2
  return (m, TermSigmaElim t' xts' e1' e2')
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
  t' <- elaborate' t >>= reduceTermPlus
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
      "the type of `" <>
      T.pack (show x) <>
      "` should be an integer type, but is:\n" <> toText (weaken t')
elaborate' (m, WeakTermFloat16 x) = do
  return (m, TermFloat16 x)
elaborate' (m, WeakTermFloat32 x) = do
  return (m, TermFloat32 x)
elaborate' (m, WeakTermFloat64 x) = do
  return (m, TermFloat64 x)
elaborate' (m, WeakTermFloat t x) = do
  t' <- elaborate' t >>= reduceTermPlus
  case t' of
    (_, TermConst (I (floatType, _))) -> do
      let x16 = realToFrac x :: Half
      let x32 = realToFrac x :: Float
      case asLowTypeMaybe floatType of
        Just (LowTypeFloat FloatSize16) -> return (m, TermFloat16 x16)
        Just (LowTypeFloat FloatSize32) -> return (m, TermFloat32 x32)
        Just (LowTypeFloat FloatSize64) -> return (m, TermFloat64 x)
        _ ->
          raiseError m $
          T.pack (show x) <> " must be float, but is " <> floatType
    _ ->
      raiseError m $
      "the type of `" <>
      T.pack (show x) <>
      "` must be a float type, but is:\n" <> toText (weaken t')
elaborate' (m, WeakTermEnum k) = do
  return (m, TermEnum k)
elaborate' (m, WeakTermEnumIntro x) = do
  return (m, TermEnumIntro x)
elaborate' (m, WeakTermEnumElim (e, t) les) = do
  e' <- elaborate' e
  let (ls, es) = unzip les
  ls' <- mapM elaborateWeakCase ls
  es' <- mapM elaborate' es
  t' <- elaborate' t >>= reduceTermPlus
  case t' of
    (_, TermEnum x) -> do
      caseCheckEnumIdentifier m x ls'
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
elaborate' (m, WeakTermCase (e, t) cxtes) = do
  e' <- elaborate' e
  cxtes' <-
    forM cxtes $ \((c, xts), body) -> do
      xts' <- mapM elaboratePlus xts
      body' <- elaborate' body
      return ((c, xts'), body')
  -- t' <- elaborate' t >>= reduceTermPlus
  t' <- elaborate' t
  t'' <- reduceWeakType $ weaken t'
  case t'' of
    (_, WeakTermPiPlus name _ _ _) -> do
      eenv <- gets enumEnv
      case Map.lookup name eenv of
        Nothing -> raiseError m $ "no such inductive type defined: " <> name
        Just bis -> do
          let bs' = map (asText . fst . fst) cxtes
          let isLinear = linearCheck bs'
          let isExhaustive = length bis == length bs'
          case (isLinear, isExhaustive) of
            (False, _) -> raiseError m $ "found a non-linear pattern"
            (_, False) -> raiseError m $ "found a non-exhaustive pattern"
            (True, True) -> return (m, TermCase (e', t') cxtes')
    _ ->
      raiseError m $
      "the type of `" <>
      toText (weaken e') <>
      "` must be an inductive type, but is:\n" <> toText t''

reduceWeakType :: WeakTermPlus -> WithEnv WeakTermPlus
reduceWeakType t = do
  let t' = reduceWeakTermPlus t
  senv <- gets substEnv
  case t' of
    (m, WeakTermPiElim (_, WeakTermUpsilon (I (_, i))) args)
      | Just lam <- IntMap.lookup i senv ->
        reduceWeakType (m, WeakTermPiElim lam args)
    _ -> return t'

-- elaborate' (m, WeakTermCocase (name, args) ces) = do
--   args' <- mapM elaborate' args
--   let (cs, es) = unzip ces
--   es' <- mapM elaborate' es
--   -- _ <- undefined name cs -- fixme: check exhaustiveness
--   return (m, TermCocase (name, args') (zip cs es'))
elaborateWeakCase :: WeakCase -> WithEnv Case
elaborateWeakCase (WeakCaseInt t x) = do
  t' <- elaborate' t >>= reduceTermPlus
  case t' of
    (_, TermEnum (EnumTypeIntS size)) ->
      return $ CaseValue (EnumValueIntS size x)
    (_, TermEnum (EnumTypeIntU size)) ->
      return $ CaseValue (EnumValueIntU size x)
    _ -> do
      raiseError (fst t) $
        "the type of `" <>
        T.pack (show x) <>
        "` should be an integer type, but is:\n" <> toText (weaken t')
elaborateWeakCase (WeakCaseLabel l) = return $ CaseValue $ EnumValueLabel l
elaborateWeakCase (WeakCaseIntS t a) = return $ CaseValue $ EnumValueIntS t a
elaborateWeakCase (WeakCaseIntU t a) = return $ CaseValue $ EnumValueIntU t a
elaborateWeakCase WeakCaseDefault = return $ CaseDefault

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
