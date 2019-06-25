module Elaborate.Analyze
  ( simp
  , analyze
  , categorize
  , bindFormalArgs
  ) where

import           Control.Comonad.Cofree
import           Control.Monad.Except
import           Control.Monad.State
import qualified Data.PQueue.Min        as Q
import           System.Timeout
import qualified Text.Show.Pretty       as Pr

import           Data.Basic
import           Data.Constraint
import           Data.Env
import           Data.WeakTerm
import           Reduce.WeakTerm

analyze :: [PreConstraint] -> WithEnv ()
analyze cs = simp cs >>= mapM_ analyze'

analyze' :: PreConstraint -> WithEnv ()
analyze' c@(e1, e2) = do
  sub <- gets substitution
  case categorize c of
    ConstraintPattern _ hole _ _
      | Just e <- lookup hole sub -> do
        cs <-
          simp [(substWeakTerm [(hole, e)] e1, substWeakTerm [(hole, e)] e2)]
        analyze cs
    ConstraintQuasiPattern _ hole _ _
      | Just e <- lookup hole sub -> do
        cs <-
          simp [(substWeakTerm [(hole, e)] e1, substWeakTerm [(hole, e)] e2)]
        analyze cs
    ConstraintFlexRigid _ hole _ _
      | Just e <- lookup hole sub -> do
        cs <-
          simp [(substWeakTerm [(hole, e)] e1, substWeakTerm [(hole, e)] e2)]
        analyze cs
    ConstraintFlexFlex hole1 _ _ _
      | Just e <- lookup hole1 sub -> do
        cs <-
          simp [(substWeakTerm [(hole1, e)] e1, substWeakTerm [(hole1, e)] e2)]
        analyze cs
    ConstraintFlexFlex _ _ hole2 _
      | Just e <- lookup hole2 sub -> do
        cs <-
          simp [(substWeakTerm [(hole2, e)] e1, substWeakTerm [(hole2, e)] e2)]
        analyze cs
    ConstraintPattern s hole args e -> do
      ans <- bindFormalArgs s args e
      let newSub = [(hole, ans)]
      modify (\env -> env {substitution = compose newSub (substitution env)})
    _ -> do
      let ec = Enriched c $ categorize c
      modify (\e -> e {constraintQueue = Q.insert ec $ constraintQueue e})

simp :: [PreConstraint] -> WithEnv [PreConstraint]
simp [] = return []
simp (c@(e1, e2):cs) = do
  b <- isEq e1 e2
  if b
    then simp cs
    else simp' $ c : cs

simp' :: [PreConstraint] -> WithEnv [PreConstraint]
simp' [] = return []
simp' ((e1, e2):cs)
  | Just (_, f, es1) <- interpretAsFlex e1
  , Just (_, g, es2) <- interpretAsFlex e2
  , f == g
  , length es1 == length es2 = do
    sub <- gets substitution
    case lookup f sub of
      Nothing -> simp $ zip es1 es2 ++ cs
      Just body ->
        if all (not . hasMeta) es1 && all (not . hasMeta) es2
          then do
            let e1' = substWeakTerm [(f, body)] e1
            let e2' = substWeakTerm [(g, body)] e2
            simp $ (e1', e2') : cs
          else do
            cs' <- simp cs
            return $ (e1, e2) : cs'
simp' (c@(e1, e2):cs)
  | _ :< WeakTermPiElim _ (_ :< WeakTermUpsilon f) _ <- e1
  , _ :< WeakTermPiElim _ (_ :< WeakTermUpsilon g) _ <- e2 = do
    d1 <- depth f
    d2 <- depth g
    sub <- gets substitution
    case compare d1 d2 of
      LT -- depth(f) < depth (g)
        | Just body2 <- lookup g sub -> do
          let e2' = substWeakTerm [(g, body2)] e2
          simp $ (e1, e2') : cs
      GT -- depth(f) > depth (g)
        | Just body1 <- lookup f sub -> do
          let e1' = substWeakTerm [(f, body1)] e1
          simp $ (e1', e2) : cs
      EQ -- depth(f) = depth (g)
        | Just body1 <- lookup f sub
        , Just body2 <- lookup g sub -> do
          let e1' = substWeakTerm [(f, body1)] e1
          let e2' = substWeakTerm [(g, body2)] e2
          simp $ (e1', e2') : cs
      _ -> simp'' $ c : cs
simp' cs = simp'' cs

simp'' :: [PreConstraint] -> WithEnv [PreConstraint]
simp'' [] = return []
simp'' ((_ :< WeakTermUniv i, _ :< WeakTermUniv j):cs) = do
  insUnivConstraintEnv i j
  simp cs
simp'' ((_ :< WeakTermEpsilon l1, _ :< WeakTermEpsilon l2):cs) = do
  simpEpsilon l1 l2
  simp cs
simp'' ((_ :< WeakTermPi s1 txs1, _ :< WeakTermPi s2 txs2):cs)
  | length txs1 == length txs2 = do
    let (ts1, xs1) = unzip txs1
    vs1 <- mapM toVar' xs1
    let (ts2, xs2) = unzip txs2
    let ts2' = map (substWeakTerm (zip xs2 vs1)) ts2
    simp $ (s1, s2) : zip ts1 ts2' ++ cs
simp'' ((_ :< WeakTermPiIntro s1 txs1 body1, _ :< WeakTermPiIntro s2 txs2 body2):cs) = do
  let (ts1, xs1) = unzip txs1
  vs1 <- mapM toVar' xs1
  let (ts2, xs2) = unzip txs2
  let ts2' = map (substWeakTerm (zip xs2 vs1)) ts2
  simp $ (s1, s2) : (body1, body2) : zip ts1 ts2' ++ cs
simp'' ((_ :< WeakTermPiIntro s txs body1, e2):cs) = do
  let (_, xs) = unzip txs
  vs <- mapM toVar' xs
  appMeta <- newNameWith "meta"
  simp $ (body1, appMeta :< WeakTermPiElim s e2 vs) : cs
simp'' ((e1, e2@(_ :< WeakTermPiIntro {})):cs) = simp $ (e2, e1) : cs
simp'' ((_ :< WeakTermSigma s1 txs1, _ :< WeakTermSigma s2 txs2):cs)
  | length txs1 == length txs2 = do
    let (ts1, xs1) = unzip txs1
    vs1 <- mapM toVar' xs1
    let (ts2, xs2) = unzip txs2
    let ts2' = map (substWeakTerm (zip xs2 vs1)) ts2
    simp $ (s1, s2) : zip ts1 ts2' ++ cs
simp'' ((_ :< WeakTermSigmaIntro s1 es1, _ :< WeakTermSigmaIntro s2 es2):cs)
  | length es1 == length es2 = simp $ (s1, s2) : zip es1 es2 ++ cs
simp'' ((_ :< WeakTermSigmaIntro s1 es, e2):cs) = do
  prList <- projectionList s1 e2 (length es)
  simp $ zip es prList ++ cs
simp'' ((e1, e2@(_ :< WeakTermSigmaIntro _ _)):cs) = simp $ (e2, e1) : cs
simp'' ((_ :< WeakTermConst x, _ :< WeakTermConst y):cs)
  | x == y = simp cs
simp'' (c@(e1, _):cs)
  | Just _ <- interpretAsFlex e1 = do
    cs' <- simp cs
    return $ c : cs'
simp'' (c@(_, e2):cs)
  | Just _ <- interpretAsFlex e2 = do
    cs' <- simp cs
    return $ c : cs'
simp'' ((e1, e2):cs)
  | isReducible e1 = do
    me1' <- liftIO $ timeout 5000000 $ return $ reduceWeakTerm e1 -- 5 sec
    case me1' of
      Just e1' -> simp $ (e1', e2) : cs
      Nothing -> do
        let e1' = toDTerm e1
        let e2' = toDTerm e2
        throwError $ "cannot simplify [TIMEOUT]:\n" ++ Pr.ppShow (e1', e2')
simp'' ((e1, e2):cs)
  | isReducible e2 = simp $ (e2, e1) : cs
simp'' ((e1, e2):cs) = do
  sub <- gets substitution
  case (e1, e2) of
    (_ :< WeakTermPiElim _ (_ :< WeakTermUpsilon x) _, _)
      | Just e <- lookup x sub -> simp $ (substWeakTerm [(x, e)] e1, e2) : cs
    (_, _ :< WeakTermPiElim _ (_ :< WeakTermUpsilon y) _)
      | Just e <- lookup y sub -> simp $ (e1, substWeakTerm [(y, e)] e2) : cs
    _ -> throwError $ "cannot simplify:\n" ++ Pr.ppShow (toDTerm e1, toDTerm e2)

simpEpsilon :: WeakEpsilon -> WeakEpsilon -> WithEnv ()
simpEpsilon (WeakEpsilonIdentifier x) (WeakEpsilonIdentifier y)
  | x == y = return ()
simpEpsilon (WeakEpsilonIdentifier _) (WeakEpsilonHole _) = undefined
simpEpsilon (WeakEpsilonHole _) (WeakEpsilonIdentifier _) = undefined
simpEpsilon _ _ = throwError "cannot simplify (simpEpsilon)"

categorize :: PreConstraint -> Constraint
categorize (_ :< WeakTermUpsilon x, e2) = ConstraintBeta x e2
categorize (e1, e2@(_ :< WeakTermUpsilon _)) = categorize (e2, e1)
categorize (e1, e2)
  | _ :< WeakTermPiElim s1 (_ :< WeakTermUpsilon x1) es1 <- e1
  , _ :< WeakTermPiElim s2 (_ :< WeakTermUpsilon x2) es2 <- e2
  , x1 == x2
  , length es1 == length es2 = ConstraintDelta x1 (s1, es1) (s2, es2)
categorize (e1, e2)
  | Just (s, x, args) <- interpretAsQuasiPattern e1
  , let (fvs, fmvs) = varAndHole e2
  , affineCheck args fvs && x `notElem` fmvs = ConstraintPattern s x args e2
categorize (e1, e2)
  | Just (_, x, args) <- interpretAsQuasiPattern e2
  , let (fvs, fmvs) = varAndHole e1
  , affineCheck args fvs && x `notElem` fmvs = categorize (e2, e1)
categorize (e1, e2)
  | Just (s, x, args) <- interpretAsQuasiPattern e1 =
    ConstraintQuasiPattern s x args e2
categorize (e1, e2)
  | Just _ <- interpretAsQuasiPattern e2 = categorize (e2, e1)
categorize (e1, e2)
  | Just (s1, x, args1) <- interpretAsFlex e1
  , Just (s2, y, args2) <- interpretAsFlex e2 =
    ConstraintFlexFlex x (s1, args1) y (s2, args2)
categorize (e1, e2)
  | Just (s, x, args) <- interpretAsFlex e1 = ConstraintFlexRigid s x args e2
categorize (e1, e2)
  | Just _ <- interpretAsFlex e2 = categorize (e2, e1)
categorize _ = error "categorize: invalid argument"

isEq :: WeakTerm -> WeakTerm -> WithEnv Bool
isEq (_ :< WeakTermUpsilon x1) (_ :< WeakTermUpsilon x2) = return $ x1 == x2
isEq (_ :< WeakTermPi s1 txs1) (_ :< WeakTermPi s2 txs2) = do
  b1 <- isEq s1 s2
  b2 <- isEqSigma txs1 txs2
  return $ b1 && b2
isEq (_ :< WeakTermPiIntro s1 txs1 e1) (_ :< WeakTermPiIntro s2 txs2 e2) = do
  b1 <- isEq s1 s2
  let (ts1, xs1) = unzip txs1
  let (ts2, xs2) = unzip txs2
  bs1 <- zipWithM isEq ts1 ts2
  metaList <- mapM (const $ newNameWith "meta") xs1
  let vs = map (\(meta, x) -> meta :< WeakTermUpsilon x) $ zip metaList xs1
  b2 <- isEq e1 $ substWeakTerm (zip xs2 vs) e2
  return $ b1 && and bs1 && b2
isEq (_ :< WeakTermPiElim s1 e1 es1) (_ :< WeakTermPiElim s2 e2 es2) = do
  b1 <- isEq s1 s2
  b2 <- isEq e1 e2
  bs <- zipWithM isEq es1 es2
  return $ b1 && b2 && and bs
isEq (_ :< WeakTermSigma s1 txs1) (_ :< WeakTermSigma s2 txs2) = do
  b1 <- isEq s1 s2
  b2 <- isEqSigma txs1 txs2
  return $ b1 && b2
isEq (_ :< WeakTermSigmaIntro s1 es1) (_ :< WeakTermSigmaIntro s2 es2)
  | length es1 == length es2 = do
    b1 <- isEq s1 s2
    bs <- zipWithM isEq es1 es2
    return $ b1 && and bs
isEq (_ :< WeakTermSigmaElim s1 txs1 e11 e12) (_ :< WeakTermSigmaElim s2 txs2 e21 e22)
  | length txs1 == length txs2 = do
    metaList <- mapM (const $ newNameWith "meta") txs1
    let vs =
          map (\(meta, (_, x)) -> meta :< WeakTermUpsilon x) $ zip metaList txs1
    let e22' = substWeakTerm (zip (map snd txs2) vs) e22
    b1 <- isEq s1 s2
    b2 <- isEq e11 e21
    b3 <- isEq e12 e22'
    return $ b1 && b2 && b3
isEq (_ :< WeakTermEpsilon l1) (_ :< WeakTermEpsilon l2) =
  return $ isEqEpsilon l1 l2
isEq (_ :< WeakTermEpsilonIntro i1) (_ :< WeakTermEpsilonIntro i2) =
  return $ i1 == i2
isEq (_ :< WeakTermEpsilonElim (t1, x1) e1 bs1) (_ :< WeakTermEpsilonElim (t2, x2) e2 bs2) = do
  b1 <- isEq e1 e2
  b2 <- isEqBranch bs1 bs2
  return $ b1 && b2
isEq (_ :< WeakTermUniv l1) (_ :< WeakTermUniv l2) = return $ l1 == l2
isEq (_ :< WeakTermConst t1) (_ :< WeakTermConst t2) = return $ t1 == t2
isEq (_ :< WeakTermRec (t1, x1) e1) (_ :< WeakTermRec (t2, x2) e2) = do
  b1 <- isEq t1 t2
  vx <- toVar' x1
  b2 <- isEq e1 $ substWeakTerm [(x2, vx)] e2
  return $ b1 && b2
isEq (_ :< WeakTermHole x1) (_ :< WeakTermHole x2) = return $ x1 == x2
isEq _ _ = return False

isEqSigma ::
     [(WeakTerm, Identifier)] -> [(WeakTerm, Identifier)] -> WithEnv Bool
isEqSigma [] [] = return True
isEqSigma ((tx, x):txs) ((ty, y):tys) = do
  vx <- toVar' x
  b1 <- isEq tx ty
  let (ts, ys) = unzip tys
  let ts' = map (substWeakTerm [(y, vx)]) ts
  let tys' = zip ts' ys
  b2 <- isEqSigma txs tys'
  return $ b1 && b2
isEqSigma _ _ = return False

isEqEpsilon :: WeakEpsilon -> WeakEpsilon -> Bool
isEqEpsilon = undefined

isEqBranch :: [(Case, WeakTerm)] -> [(Case, WeakTerm)] -> WithEnv Bool
isEqBranch [] [] = return True
isEqBranch ((CaseLiteral (LiteralLabel x1), e1):es1) ((CaseLiteral (LiteralLabel x2), e2):es2)
  | x1 == x2 = isEqBranch' e1 es1 e2 es2
isEqBranch ((CaseLiteral (LiteralInteger i1), e1):es1) ((CaseLiteral (LiteralInteger i2), e2):es2)
  | i1 == i2 = isEqBranch' e1 es1 e2 es2
isEqBranch ((CaseLiteral (LiteralFloat i1), e1):es1) ((CaseLiteral (LiteralFloat i2), e2):es2)
  | i1 == i2 = isEqBranch' e1 es1 e2 es2
isEqBranch ((CaseDefault, e1):es1) ((CaseDefault, e2):es2) =
  isEqBranch' e1 es1 e2 es2
isEqBranch _ _ = return False

isEqBranch' ::
     WeakTerm
  -> [(Case, WeakTerm)]
  -> WeakTerm
  -> [(Case, WeakTerm)]
  -> WithEnv Bool
isEqBranch' e1 es1 e2 es2 = do
  b1 <- isEq e1 e2
  b2 <- isEqBranch es1 es2
  return $ b1 && b2

toVar' :: Identifier -> WithEnv WeakTerm
toVar' x = do
  meta <- newNameWith "meta"
  return $ meta :< WeakTermUpsilon x

affineCheck :: [Identifier] -> [Identifier] -> Bool
affineCheck xs = affineCheck' xs xs

affineCheck' :: [Identifier] -> [Identifier] -> [Identifier] -> Bool
affineCheck' _ [] _ = True
affineCheck' xs (y:ys) fvs =
  if y `notElem` fvs
    then affineCheck' xs ys fvs
    else null (isLinear y xs) && affineCheck' xs ys fvs

isLinear :: Identifier -> [Identifier] -> [Identifier]
isLinear x xs =
  if length (filter (== x) xs) == 1
    then []
    else [x]

projectionList :: WeakSortal -> WeakTerm -> Int -> WithEnv [WeakTerm]
projectionList s e n = do
  xs <- forM [1 .. n] $ \_ -> newNameWith "pr"
  ts <- mapM (const newHole) xs
  metaList <- mapM (const newName) xs
  let varList = map (\(meta, x) -> meta :< WeakTermUpsilon x) $ zip metaList xs
  forM varList $ \x -> do
    meta <- newName
    return $ meta :< WeakTermSigmaElim s (zip ts xs) e x

bindFormalArgs :: WeakSortal -> [Identifier] -> WeakTerm -> WithEnv WeakTerm
bindFormalArgs s xs e = do
  ts <- mapM (const newHole) xs
  meta <- newNameWith "meta"
  return $ meta :< WeakTermPiIntro s (zip ts xs) e

hasMeta :: WeakTerm -> Bool
hasMeta (_ :< WeakTermUpsilon _) = False
hasMeta (_ :< WeakTermPi s txs) = do
  let (ts, _) = unzip txs
  hasMeta s || any hasMeta ts
hasMeta (_ :< WeakTermPiIntro s _ e) = hasMeta s || hasMeta e
hasMeta (_ :< WeakTermPiElim s e es) = hasMeta s || hasMeta e || any hasMeta es
hasMeta (_ :< WeakTermSigma s txs) = do
  let (ts, _) = unzip txs
  hasMeta s || any hasMeta ts
hasMeta (_ :< WeakTermSigmaIntro s es) = hasMeta s || any hasMeta es
hasMeta (_ :< WeakTermSigmaElim s _ e1 e2) =
  hasMeta s || hasMeta e1 || hasMeta e2
hasMeta (_ :< WeakTermEpsilon _) = False
hasMeta (_ :< WeakTermEpsilonIntro _) = False
hasMeta (_ :< WeakTermEpsilonElim _ e branchList) = do
  let (_, es) = unzip branchList
  any hasMeta (e : es)
hasMeta (_ :< WeakTermUniv _) = False
hasMeta (_ :< WeakTermConst _) = False
hasMeta (_ :< WeakTermRec _ e) = hasMeta e
hasMeta (_ :< WeakTermHole _) = True

depth :: Identifier -> WithEnv Int
depth x = do
  sub <- gets substitution
  case lookup x sub of
    Nothing -> return 0
    Just e -> do
      ds <- mapM depth $ varWeakTerm e
      return $ 1 + maximum ds

interpretAsQuasiPattern ::
     WeakTerm -> Maybe (WeakSortal, Identifier, [Identifier])
interpretAsQuasiPattern (_ :< WeakTermPiElim s (_ :< WeakTermHole x) es) = do
  xs <- mapM interpretAsUpsilon es
  return (s, x, xs)
interpretAsQuasiPattern _ = Nothing

interpretAsUpsilon :: WeakTerm -> Maybe Identifier
interpretAsUpsilon (_ :< WeakTermUpsilon x) = Just x
interpretAsUpsilon _                        = Nothing

interpretAsFlex :: WeakTerm -> Maybe (WeakSortal, Identifier, [WeakTerm])
interpretAsFlex (_ :< WeakTermPiElim s (_ :< WeakTermHole x) es) =
  Just (s, x, es)
interpretAsFlex _ = Nothing
