module Elaborate.Analyze
  ( simp
  , analyze
  , categorize
  ) where

import           Control.Comonad.Cofree
import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Trans.Except
import qualified Data.PQueue.Min            as Q
import qualified Text.Show.Pretty           as Pr

import           Data.Basic
import           Data.Constraint
import           Data.Env
import           Data.Neut
import           Reduce.Neut
import           Util

analyze :: [PreConstraint] -> WithEnv ()
analyze cs = simp cs >>= mapM_ analyze'

analyze' :: PreConstraint -> WithEnv ()
analyze' c@(e1, e2) = do
  sub <- gets substitution
  case categorize c of
    ConstraintPattern hole _ _
      | Just e <- lookup hole sub -> do
        cs <- simp [(subst [(hole, e)] e1, subst [(hole, e)] e2)]
        analyze cs
    ConstraintQuasiPattern hole _ _
      | Just e <- lookup hole sub -> do
        cs <- simp [(subst [(hole, e)] e1, subst [(hole, e)] e2)]
        analyze cs
    ConstraintFlexRigid hole _ _
      | Just e <- lookup hole sub -> do
        cs <- simp [(subst [(hole, e)] e1, subst [(hole, e)] e2)]
        analyze cs
    ConstraintFlexFlex hole1 _ _ _
      | Just e <- lookup hole1 sub -> do
        cs <- simp [(subst [(hole1, e)] e1, subst [(hole1, e)] e2)]
        analyze cs
    ConstraintFlexFlex _ _ hole2 _
      | Just e <- lookup hole2 sub -> do
        cs <- simp [(subst [(hole2, e)] e1, subst [(hole2, e)] e2)]
        analyze cs
    ConstraintPattern hole args e -> do
      ans <- bindFormalArgs' args e
      modify (\e -> e {substitution = compose [(hole, ans)] (substitution e)})
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
      Nothing -> simp $ (zip es1 es2) ++ cs
      Just body ->
        if all (not . hasMeta) es1 && all (not . hasMeta) es2
          then do
            let e1' = subst [(f, body)] e1
            let e2' = subst [(g, body)] e2
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
          let e2' = subst [(g, body2)] e2
          simp $ (e1, e2') : cs
      GT -- depth(f) > depth (g)
        | Just body1 <- lookup f sub -> do
          let e1' = subst [(f, body1)] e1
          simp $ (e1', e2) : cs
      EQ -- depth(f) = depth (g)
        | Just body1 <- lookup f sub
        , Just body2 <- lookup g sub -> do
          let e1' = subst [(f, body1)] e1
          let e2' = subst [(g, body2)] e2
          simp $ (e1', e2') : cs
      _ -> simp'' $ c : cs
simp' cs = simp'' cs

simp'' :: [PreConstraint] -> WithEnv [PreConstraint]
simp'' [] = return []
simp'' ((_ :< NeutConst x, _ :< NeutConst y):cs)
  | x == y = simp cs
simp'' ((_ :< NeutPi (x, tdom1) tcod1, _ :< NeutPi (y, tdom2) tcod2):cs) = do
  var <- toVar' x
  cs' <- sConstraint [(y, var)] cs >>= simp
  simp $ (tdom1, tdom2) : (tcod1, subst [(y, var)] tcod2) : cs'
simp'' ((_ :< NeutPiIntro (x, _) body1, _ :< NeutPiIntro (y, _) body2):cs) = do
  var <- toVar' x
  simp $ (body1, subst [(y, var)] body2) : cs
simp'' ((_ :< NeutPiIntro (x, _) body1, e2):cs) = do
  var <- toVar' x
  appMeta <- newNameWith "meta"
  let app = appMeta :< NeutPiElim e2 var
  simp $ (body1, app) : cs
simp'' ((e1, e2@(_ :< NeutPiIntro _ _)):cs) = simp $ (e2, e1) : cs
simp'' ((_ :< NeutSigma xts, _ :< NeutSigma yts):cs)
  | length xts == length yts = do
    let (xs, txs) = unzip xts
    vs <- mapM toVar' xs
    let (ys, tys) = unzip yts
    let tys' = map (subst (zip ys vs)) tys
    simp $ zip txs tys' ++ cs
simp'' ((_ :< NeutSigmaIntro es1, _ :< NeutSigmaIntro es2):cs)
  | length es1 == length es2 = simp $ zip es1 es2 ++ cs
simp'' ((_ :< NeutSigmaIntro es, e2):cs) = do
  prList <- projectionList e2 (length es)
  simp $ zip es prList ++ cs
simp'' ((e1, e2@(_ :< NeutSigmaIntro _)):cs) = simp $ (e2, e1) : cs
simp'' ((_ :< NeutIndex l1, _ :< NeutIndex l2):cs)
  | l1 == l2 = simp cs
simp'' ((_ :< NeutUniv i, _ :< NeutUniv j):cs) = do
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
  | isReducible e1 = do
    e1' <- reduce e1
    simp $ (e1', e2) : cs
simp'' ((e1, e2):cs)
  | isReducible e2 = simp $ (e2, e1) : cs
simp'' (c@(e1, e2):cs) = do
  let mx = headMeta'' e1
  let my = headMeta'' e2
  sub <- gets substitution
  case (mx, my) of
    (Just x, _)
      | Just e <- lookup x sub -> simp $ (subst [(x, e)] e1, e2) : cs
    (_, Just y)
      | Just e <- lookup y sub -> simp $ (e1, subst [(y, e)] e2) : cs
    _ -> throwError $ "cannot simplify:\n" ++ Pr.ppShow c

categorize :: PreConstraint -> Constraint
categorize (_ :< NeutVar x, e2) = ConstraintBeta x e2
categorize (e1, e2@(_ :< NeutVar _)) = categorize (e2, e1)
categorize (e1, e2)
  | (_ :< NeutVar x, metaArgs1) <- toPiElimSeq e1
  , (_ :< NeutVar y, metaArgs2) <- toPiElimSeq e2
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

isEq :: Neut -> Neut -> WithEnv Bool
isEq (_ :< NeutVar x1) (_ :< NeutVar x2) = return $ x1 == x2
isEq (_ :< NeutPi (x1, t11) t12) (_ :< NeutPi (x2, t21) t22) = do
  vx <- toVar' x1
  b1 <- isEq t11 t21
  b2 <- isEq t12 $ subst [(x2, vx)] t22
  return $ b1 && b2
isEq (_ :< NeutPiIntro (x1, t1) e1) (_ :< NeutPiIntro (x2, t2) e2) = do
  vx <- toVar' x1
  b1 <- isEq t1 t2
  b2 <- isEq e1 $ subst [(x2, vx)] e2
  return $ b1 && b2
isEq (_ :< NeutPiElim e11 e12) (_ :< NeutPiElim e21 e22) = do
  b1 <- isEq e11 e21
  b2 <- isEq e12 e22
  return $ b1 && b2
isEq (_ :< NeutSigma xts) (_ :< NeutSigma yts) = isEqSigma xts yts
isEq (_ :< NeutSigmaIntro es1) (_ :< NeutSigmaIntro es2)
  | length es1 == length es2 = do
    bs <- zipWithM isEq es1 es2
    return $ and bs
isEq (_ :< NeutSigmaElim e11 xs1 e12) (_ :< NeutSigmaElim e21 xs2 e22)
  | length xs1 == length xs2 = do
    metaList <- mapM (const $ newNameWith "meta") xs1
    let vs = map (\(meta, x) -> meta :< NeutVar x) $ zip metaList xs1
    let sub = zip xs2 vs
    let e22' = subst sub e22
    b1 <- isEq e11 e21
    b2 <- isEq e12 e22'
    return $ b1 && b2
isEq (_ :< NeutIndex l1) (_ :< NeutIndex l2) = return $ l1 == l2
isEq (_ :< NeutIndexIntro i1) (_ :< NeutIndexIntro i2) = return $ i1 == i2
isEq (_ :< NeutIndexElim e1 bs1) (_ :< NeutIndexElim e2 bs2) = do
  b1 <- isEq e1 e2
  b2 <- isEqBranch bs1 bs2
  return $ b1 && b2
isEq (_ :< NeutUniv l1) (_ :< NeutUniv l2) = return $ l1 == l2
isEq (_ :< NeutConst t1) (_ :< NeutConst t2) = return $ t1 == t2
isEq (_ :< NeutMu x1 e1) (_ :< NeutMu x2 e2) = do
  vx <- toVar' x1
  isEq e1 $ subst [(x2, vx)] e2
isEq (_ :< NeutHole x1) (_ :< NeutHole x2) = return $ x1 == x2
isEq _ _ = return False

isEqSigma :: [(Identifier, Neut)] -> [(Identifier, Neut)] -> WithEnv Bool
isEqSigma [] [] = return True
isEqSigma ((x, tx):xts) ((y, ty):yts) = do
  vx <- toVar' x
  b1 <- isEq tx ty
  let (ys, ts) = unzip yts
  let ts' = map (subst [(y, vx)]) ts
  let yts' = zip ys ts'
  b2 <- isEqSigma xts yts'
  return $ b1 && b2
isEqSigma _ _ = return False

isEqBranch :: [(Index, Neut)] -> [(Index, Neut)] -> WithEnv Bool
isEqBranch [] [] = return True
isEqBranch ((IndexLabel x1, e1):es1) ((IndexLabel x2, e2):es2)
  | x1 == x2 = do
    b1 <- isEq e1 e2
    b2 <- isEqBranch es1 es2
    return $ b1 && b2
isEqBranch ((IndexInteger i1, e1):es1) ((IndexInteger i2, e2):es2)
  | i1 == i2 = do
    b1 <- isEq e1 e2
    b2 <- isEqBranch es1 es2
    return $ b1 && b2
isEqBranch ((IndexFloat i1, e1):es1) ((IndexFloat i2, e2):es2)
  | i1 == i2 = do
    b1 <- isEq e1 e2
    b2 <- isEqBranch es1 es2
    return $ b1 && b2
isEqBranch ((IndexDefault, e1):es1) ((IndexDefault, e2):es2) = do
  b1 <- isEq e1 e2
  b2 <- isEqBranch es1 es2
  return $ b1 && b2
isEqBranch _ _ = return False

toVar' :: Identifier -> WithEnv Neut
toVar' x = do
  meta <- newNameWith "meta"
  return $ meta :< NeutVar x

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

projectionList :: Neut -> Int -> WithEnv [Neut]
projectionList e count = do
  xs <- forM [1 .. count] $ \_ -> newNameWith "pr"
  metaList <- mapM (const newName) xs
  let varList = map (\(meta, x) -> meta :< NeutVar x) $ zip metaList xs
  forM varList $ \x -> do
    meta <- newName
    return $ meta :< NeutSigmaElim e xs x

sConstraint :: Subst -> [PreConstraint] -> WithEnv [PreConstraint]
sConstraint s cs = do
  let (ts1, ts2) = unzip cs
  let ts1' = map (subst s) ts1
  let ts2' = map (subst s) ts2
  return $ zip ts1' ts2'

hasMeta :: Neut -> Bool
hasMeta (_ :< NeutVar _) = False
hasMeta (_ :< NeutPi (_, tdom) tcod) = hasMeta tdom || hasMeta tcod
hasMeta (_ :< NeutPiIntro _ e) = hasMeta e
hasMeta (_ :< NeutPiElim e1 e2) = hasMeta e1 || hasMeta e2
hasMeta (_ :< NeutSigma xts) = do
  let (_, ts) = unzip xts
  any hasMeta ts
hasMeta (_ :< NeutSigmaIntro es) = any hasMeta es
hasMeta (_ :< NeutSigmaElim e1 _ e2) = hasMeta e1 || hasMeta e2
hasMeta (_ :< NeutIndex _) = False
hasMeta (_ :< NeutIndexIntro _) = False
hasMeta (_ :< NeutIndexElim e branchList) = do
  let (_, es) = unzip branchList
  any hasMeta (e : es)
hasMeta (_ :< NeutUniv _) = False
hasMeta (_ :< NeutConst _) = False
hasMeta (_ :< NeutMu _ e) = hasMeta e
hasMeta (_ :< NeutHole _) = True

depth :: Identifier -> WithEnv Int
depth x = do
  sub <- gets substitution
  case lookup x sub of
    Nothing -> return 0
    Just e -> do
      let vs = var e
      ds <- mapM depth vs
      return $ 1 + maximum ds

headMeta :: [Identifier] -> Neut -> Maybe (Identifier, [Identifier])
headMeta args (_ :< NeutPiElim e1 (_ :< NeutVar x)) = headMeta (x : args) e1
headMeta args (_ :< NeutHole x)                     = Just (x, args)
headMeta _ _                                        = Nothing

headMeta' :: [Neut] -> Neut -> Maybe (Identifier, [Neut])
headMeta' args (_ :< NeutPiElim e1 e2) = headMeta' (e2 : args) e1
headMeta' args (_ :< NeutHole x)       = Just (x, args)
headMeta' _ _                          = Nothing

headMeta'' :: Neut -> Maybe Identifier
headMeta'' (_ :< NeutVar x)         = Just x
headMeta'' (_ :< NeutPiElim e1 _)   = headMeta'' e1
headMeta'' (_ :< NeutIndexElim e _) = headMeta'' e
headMeta'' _                        = Nothing
