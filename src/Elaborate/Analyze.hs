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
    ConstraintPattern hole _ _
      | Just e <- lookup hole sub -> do
        cs <-
          simp [(substWeakTerm [(hole, e)] e1, substWeakTerm [(hole, e)] e2)]
        analyze cs
    ConstraintQuasiPattern hole _ _
      | Just e <- lookup hole sub -> do
        cs <-
          simp [(substWeakTerm [(hole, e)] e1, substWeakTerm [(hole, e)] e2)]
        analyze cs
    ConstraintFlexRigid hole _ _
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
    ConstraintPattern hole args e -> do
      ans <- bindFormalArgs args e
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
  | Just (f, es1) <- headMeta' [] e1
  , Just (g, es2) <- headMeta' [] e2
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
  | Just f <- headMeta'' e1
  , Just g <- headMeta'' e2 = do
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
simp'' ((_ :< WeakTermConst x, _ :< WeakTermConst y):cs)
  | x == y = simp cs
simp'' ((_ :< WeakTermPi (x, tdom1) tcod1, _ :< WeakTermPi (y, tdom2) tcod2):cs) = do
  var <- toVar' x
  cs' <- sConstraint [(y, var)] cs >>= simp
  simp $ (tdom1, tdom2) : (tcod1, substWeakTerm [(y, var)] tcod2) : cs'
simp'' ((_ :< WeakTermPiIntro (x, _) body1, _ :< WeakTermPiIntro (y, _) body2):cs) = do
  var <- toVar' x
  simp $ (body1, substWeakTerm [(y, var)] body2) : cs
simp'' ((_ :< WeakTermPiIntro (x, _) body1, e2):cs) = do
  var <- toVar' x
  appMeta <- newNameWith "meta"
  let app = appMeta :< WeakTermPiElim e2 var
  simp $ (body1, app) : cs
simp'' ((e1, e2@(_ :< WeakTermPiIntro _ _)):cs) = simp $ (e2, e1) : cs
simp'' ((_ :< WeakTermSigma xts, _ :< WeakTermSigma yts):cs)
  | length xts == length yts = do
    let (xs, txs) = unzip xts
    vs <- mapM toVar' xs
    let (ys, tys) = unzip yts
    let tys' = map (substWeakTerm (zip ys vs)) tys
    simp $ zip txs tys' ++ cs
simp'' ((_ :< WeakTermSigmaIntro es1, _ :< WeakTermSigmaIntro es2):cs)
  | length es1 == length es2 = simp $ zip es1 es2 ++ cs
simp'' ((_ :< WeakTermSigmaIntro es, e2):cs) = do
  prList <- projectionList e2 (length es)
  simp $ zip es prList ++ cs
simp'' ((e1, e2@(_ :< WeakTermSigmaIntro _)):cs) = simp $ (e2, e1) : cs
simp'' ((_ :< WeakTermIndex l1, _ :< WeakTermIndex l2):cs)
  | l1 == l2 = simp cs
simp'' ((_ :< WeakTermUniv i, _ :< WeakTermUniv j):cs) = do
  insUnivConstraintEnv i j
  simp cs
simp'' (c@(e1, _):cs)
  | Just _ <- headMeta' [] e1 = do
    cs' <- simp cs
    return $ c : cs'
simp'' (c@(_, e2):cs)
  | Just _ <- headMeta' [] e2 = do
    cs' <- simp cs
    return $ c : cs'
simp'' ((e1, e2):cs)
  | isNonRecReducible e1 = do
    e1' <- reduceWeakTermExceptMu e1
    simp $ (e1', e2) : cs
simp'' ((e1, e2):cs)
  | isNonRecReducible e2 = simp $ (e2, e1) : cs
simp'' (c@(e1, e2):cs) = do
  let mx = headMeta'' e1
  let my = headMeta'' e2
  sub <- gets substitution
  case (mx, my) of
    (Just x, _)
      | Just e <- lookup x sub -> simp $ (substWeakTerm [(x, e)] e1, e2) : cs
    (_, Just y)
      | Just e <- lookup y sub -> simp $ (e1, substWeakTerm [(y, e)] e2) : cs
    _ -> throwError $ "cannot simplify:\n" ++ Pr.ppShow c

categorize :: PreConstraint -> Constraint
categorize (_ :< WeakTermVar x, e2) = ConstraintBeta x e2
categorize (e1, e2@(_ :< WeakTermVar _)) = categorize (e2, e1)
categorize (e1, e2)
  | (_ :< WeakTermVar x, metaArgs1) <- toWeakTermPiElimSeq e1
  , (_ :< WeakTermVar y, metaArgs2) <- toWeakTermPiElimSeq e2
  , x == y
  , length metaArgs1 == length metaArgs2 =
    ConstraintDelta x (map snd metaArgs1) (map snd metaArgs2)
categorize (e1, e2)
  | Just (x, args) <- headMeta [] e1
  , let (fvs, fmvs) = varAndHole e2
  , affineCheck args fvs && x `notElem` fmvs = ConstraintPattern x args e2
categorize (e1, e2)
  | Just (x, args) <- headMeta [] e1
  , let (fvs, fmvs) = varAndHole e2
  , affineCheck args fvs && x `notElem` fmvs = categorize (e2, e1)
categorize (e1, e2)
  | Just (x, args) <- headMeta [] e1 = ConstraintQuasiPattern x args e2
categorize (e1, e2)
  | Just _ <- headMeta [] e2 = categorize (e2, e1)
categorize (e1, e2)
  | Just (x, args1) <- headMeta' [] e1
  , Just (y, args2) <- headMeta' [] e2 = ConstraintFlexFlex x args1 y args2
categorize (e1, e2)
  | Just (x, args) <- headMeta' [] e1 = ConstraintFlexRigid x args e2
categorize (e1, e2)
  | Just _ <- headMeta' [] e2 = categorize (e2, e1)
categorize c = error $ "categorize: invalid argument:\n" ++ Pr.ppShow c

isEq :: WeakTerm -> WeakTerm -> WithEnv Bool
isEq (_ :< WeakTermVar x1) (_ :< WeakTermVar x2) = return $ x1 == x2
isEq (_ :< WeakTermPi (x1, t11) t12) (_ :< WeakTermPi (x2, t21) t22) = do
  vx <- toVar' x1
  b1 <- isEq t11 t21
  b2 <- isEq t12 $ substWeakTerm [(x2, vx)] t22
  return $ b1 && b2
isEq (_ :< WeakTermPiIntro (x1, t1) e1) (_ :< WeakTermPiIntro (x2, t2) e2) = do
  vx <- toVar' x1
  b1 <- isEq t1 t2
  b2 <- isEq e1 $ substWeakTerm [(x2, vx)] e2
  return $ b1 && b2
isEq (_ :< WeakTermPiElim e11 e12) (_ :< WeakTermPiElim e21 e22) = do
  b1 <- isEq e11 e21
  b2 <- isEq e12 e22
  return $ b1 && b2
isEq (_ :< WeakTermSigma xts) (_ :< WeakTermSigma yts) = isEqSigma xts yts
isEq (_ :< WeakTermSigmaIntro es1) (_ :< WeakTermSigmaIntro es2)
  | length es1 == length es2 = do
    bs <- zipWithM isEq es1 es2
    return $ and bs
isEq (_ :< WeakTermSigmaElim xs1 e11 e12) (_ :< WeakTermSigmaElim xs2 e21 e22)
  | length xs1 == length xs2 = do
    metaList <- mapM (const $ newNameWith "meta") xs1
    let vs = map (\(meta, x) -> meta :< WeakTermVar x) $ zip metaList xs1
    let sub = zip xs2 vs
    let e22' = substWeakTerm sub e22
    b1 <- isEq e11 e21
    b2 <- isEq e12 e22'
    return $ b1 && b2
isEq (_ :< WeakTermIndex l1) (_ :< WeakTermIndex l2) = return $ l1 == l2
isEq (_ :< WeakTermIndexIntro i1) (_ :< WeakTermIndexIntro i2) =
  return $ i1 == i2
isEq (_ :< WeakTermIndexElim e1 bs1) (_ :< WeakTermIndexElim e2 bs2) = do
  b1 <- isEq e1 e2
  b2 <- isEqBranch bs1 bs2
  return $ b1 && b2
isEq (_ :< WeakTermUniv l1) (_ :< WeakTermUniv l2) = return $ l1 == l2
isEq (_ :< WeakTermConst t1) (_ :< WeakTermConst t2) = return $ t1 == t2
isEq (_ :< WeakTermFix x1 e1) (_ :< WeakTermFix x2 e2) = do
  vx <- toVar' x1
  isEq e1 $ substWeakTerm [(x2, vx)] e2
isEq (_ :< WeakTermHole x1) (_ :< WeakTermHole x2) = return $ x1 == x2
isEq _ _ = return False

isEqSigma ::
     [(Identifier, WeakTerm)] -> [(Identifier, WeakTerm)] -> WithEnv Bool
isEqSigma [] [] = return True
isEqSigma ((x, tx):xts) ((y, ty):yts) = do
  vx <- toVar' x
  b1 <- isEq tx ty
  let (ys, ts) = unzip yts
  let ts' = map (substWeakTerm [(y, vx)]) ts
  let yts' = zip ys ts'
  b2 <- isEqSigma xts yts'
  return $ b1 && b2
isEqSigma _ _ = return False

isEqBranch :: [(Index, WeakTerm)] -> [(Index, WeakTerm)] -> WithEnv Bool
isEqBranch [] [] = return True
isEqBranch ((IndexLabel x1, e1):es1) ((IndexLabel x2, e2):es2)
  | x1 == x2 = isEqBranch' e1 es1 e2 es2
isEqBranch ((IndexInteger i1, e1):es1) ((IndexInteger i2, e2):es2)
  | i1 == i2 = isEqBranch' e1 es1 e2 es2
isEqBranch ((IndexFloat i1, e1):es1) ((IndexFloat i2, e2):es2)
  | i1 == i2 = isEqBranch' e1 es1 e2 es2
isEqBranch ((IndexDefault, e1):es1) ((IndexDefault, e2):es2) =
  isEqBranch' e1 es1 e2 es2
isEqBranch _ _ = return False

isEqBranch' ::
     WeakTerm
  -> [(Index, WeakTerm)]
  -> WeakTerm
  -> [(Index, WeakTerm)]
  -> WithEnv Bool
isEqBranch' e1 es1 e2 es2 = do
  b1 <- isEq e1 e2
  b2 <- isEqBranch es1 es2
  return $ b1 && b2

toVar' :: Identifier -> WithEnv WeakTerm
toVar' x = do
  meta <- newNameWith "meta"
  return $ meta :< WeakTermVar x

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

projectionList :: WeakTerm -> Int -> WithEnv [WeakTerm]
projectionList e n = do
  xs <- forM [1 .. n] $ \_ -> newNameWith "pr"
  metaList <- mapM (const newName) xs
  let varList = map (\(meta, x) -> meta :< WeakTermVar x) $ zip metaList xs
  forM varList $ \x -> do
    meta <- newName
    return $ meta :< WeakTermSigmaElim xs e x

sConstraint :: SubstWeakTerm -> [PreConstraint] -> WithEnv [PreConstraint]
sConstraint s cs = do
  let (ts1, ts2) = unzip cs
  let ts1' = map (substWeakTerm s) ts1
  let ts2' = map (substWeakTerm s) ts2
  return $ zip ts1' ts2'

bindFormalArgs :: [Identifier] -> WeakTerm -> WithEnv WeakTerm
bindFormalArgs [] terminal = return terminal
bindFormalArgs (arg:xs) c = do
  tmp <- bindFormalArgs xs c
  meta <- newNameWith "meta"
  h <- newNameWith "hole"
  holeMeta <- newNameWith "meta"
  return $ meta :< WeakTermPiIntro (arg, holeMeta :< WeakTermHole h) tmp

hasMeta :: WeakTerm -> Bool
hasMeta (_ :< WeakTermVar _) = False
hasMeta (_ :< WeakTermPi (_, tdom) tcod) = hasMeta tdom || hasMeta tcod
hasMeta (_ :< WeakTermPiIntro _ e) = hasMeta e
hasMeta (_ :< WeakTermPiElim e1 e2) = hasMeta e1 || hasMeta e2
hasMeta (_ :< WeakTermSigma xts) = do
  let (_, ts) = unzip xts
  any hasMeta ts
hasMeta (_ :< WeakTermSigmaIntro es) = any hasMeta es
hasMeta (_ :< WeakTermSigmaElim _ e1 e2) = hasMeta e1 || hasMeta e2
hasMeta (_ :< WeakTermIndex _) = False
hasMeta (_ :< WeakTermIndexIntro _) = False
hasMeta (_ :< WeakTermIndexElim e branchList) = do
  let (_, es) = unzip branchList
  any hasMeta (e : es)
hasMeta (_ :< WeakTermUniv _) = False
hasMeta (_ :< WeakTermConst _) = False
hasMeta (_ :< WeakTermFix _ e) = hasMeta e
hasMeta (_ :< WeakTermHole _) = True

depth :: Identifier -> WithEnv Int
depth x = do
  sub <- gets substitution
  case lookup x sub of
    Nothing -> return 0
    Just e -> do
      ds <- mapM depth $ varWeakTerm e
      return $ 1 + maximum ds

headMeta :: [Identifier] -> WeakTerm -> Maybe (Identifier, [Identifier])
headMeta args (_ :< WeakTermPiElim e1 (_ :< WeakTermVar x)) =
  headMeta (x : args) e1
headMeta args (_ :< WeakTermHole x) = Just (x, args)
headMeta _ _ = Nothing

headMeta' :: [WeakTerm] -> WeakTerm -> Maybe (Identifier, [WeakTerm])
headMeta' args (_ :< WeakTermPiElim e1 e2) = headMeta' (e2 : args) e1
headMeta' args (_ :< WeakTermHole x)       = Just (x, args)
headMeta' _ _                              = Nothing

headMeta'' :: WeakTerm -> Maybe Identifier
headMeta'' (_ :< WeakTermVar x)         = Just x
headMeta'' (_ :< WeakTermPiElim e1 _)   = headMeta'' e1
headMeta'' (_ :< WeakTermIndexElim e _) = headMeta'' e
headMeta'' _                            = Nothing
