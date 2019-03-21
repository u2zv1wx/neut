module Elaborate.Analyze
  ( simp
  , analyze
  , categorize
  ) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Trans.Except

import Control.Comonad.Cofree

import qualified Text.Show.Pretty as Pr

import Data
import Reduce
import Util

import Data.List

import Control.Concurrent (forkIO, threadDelay)
import Data.Maybe
import System.Timeout

import qualified Data.PQueue.Min as Q

analyze :: [PreConstraint] -> WithEnv ()
analyze cs = simp cs >>= mapM_ analyze'

analyze' :: PreConstraint -> WithEnv ()
analyze' c@(ctx, e1, e2, t) = do
  sub <- gets substitution
  case categorize c of
    Constraint _ (ConstraintPattern hole _ _) _
      | Just e <- lookup hole sub -> do
        cs <- simp [(ctx, subst [(hole, e)] e1, subst [(hole, e)] e2, t)]
        analyze cs
    Constraint _ (ConstraintQuasiPattern hole _ _) _
      | Just e <- lookup hole sub -> do
        cs <- simp [(ctx, subst [(hole, e)] e1, subst [(hole, e)] e2, t)]
        analyze cs
    Constraint _ (ConstraintFlexRigid hole _ _) _
      | Just e <- lookup hole sub -> do
        cs <- simp [(ctx, subst [(hole, e)] e1, subst [(hole, e)] e2, t)]
        analyze cs
    Constraint _ (ConstraintFlexFlex hole1 _ _ _) _
      | Just e <- lookup hole1 sub -> do
        cs <- simp [(ctx, subst [(hole1, e)] e1, subst [(hole1, e)] e2, t)]
        analyze cs
    Constraint _ (ConstraintFlexFlex _ _ hole2 _) _
      | Just e <- lookup hole2 sub -> do
        cs <- simp [(ctx, subst [(hole2, e)] e1, subst [(hole2, e)] e2, t)]
        analyze cs
    Constraint _ (ConstraintPattern hole args e) _ -> do
      ans <- bindFormalArgs' args e
      modify (\e -> e {substitution = compose [(hole, ans)] (substitution e)})
    _ -> do
      let ec = Enriched c $ categorize c
      modify (\e -> e {constraintQueue = Q.insert ec $ constraintQueue e})

simp :: [PreConstraint] -> WithEnv [PreConstraint]
simp [] = return []
simp (c@(_, e1, e2, _):cs) = do
  b <- isEq e1 e2
  if b
    then simp cs
    else simp' $ c : cs

simp' :: [PreConstraint] -> WithEnv [PreConstraint]
simp' [] = return []
simp' ((ctx, e1, e2, t):cs)
  | Just (f, es1) <- headMeta' [] e1
  , Just (g, es2) <- headMeta' [] e2
  , f == g
  , length es1 == length es2 = do
    sub <- gets substitution
    case lookup f sub of
      Nothing -> do
        let newCs = map (\(p, q) -> (ctx, p, q, t)) $ zip es1 es2
        simp $ newCs ++ cs
      Just body ->
        if all (not . hasMeta) es1 && all (not . hasMeta) es2
          then do
            let e1' = subst [(f, body)] e1
            let e2' = subst [(g, body)] e2
            simp $ (ctx, e1', e2', t) : cs
          else do
            cs' <- simp cs
            return $ (ctx, e1, e2, t) : cs'
simp' (c@(ctx, e1, e2, t):cs)
  | Just f <- headMeta'' e1
  , Just g <- headMeta'' e2 = do
    d1 <- depth f
    d2 <- depth g
    sub <- gets substitution
    case compare d1 d2 of
      LT -- depth(f) < depth (g)
        | Just body2 <- lookup g sub -> do
          let e2' = subst [(g, body2)] e2
          simp $ (ctx, e1, e2', t) : cs
      GT -- depth(f) > depth (g)
        | Just body1 <- lookup f sub -> do
          let e1' = subst [(f, body1)] e1
          simp $ (ctx, e1', e2, t) : cs
      EQ -- depth(f) = depth (g)
        | Just body1 <- lookup f sub
        , Just body2 <- lookup g sub -> do
          let e1' = subst [(f, body1)] e1
          let e2' = subst [(g, body2)] e2
          simp $ (ctx, e1', e2', t) : cs
      _ -> simp'' $ c : cs
simp' cs = simp'' cs

simp'' :: [PreConstraint] -> WithEnv [PreConstraint]
simp'' [] = return []
simp'' ((_, _ :< NeutConst x, _ :< NeutConst y, _):cs)
  | x == y = simp cs
simp'' ((ctx, _ :< NeutPi (x, tdom1) tcod1, _ :< NeutPi (y, tdom2) tcod2, univ):cs) = do
  var <- toVar' x
  cs' <- sConstraint [(y, var)] cs >>= simp
  simp $
    (ctx, tdom1, tdom2, univ) :
    (ctx ++ [x], tcod1, subst [(y, var)] tcod2, univ) : cs'
simp'' ((ctx, _ :< NeutPiIntro (x, _) body1, _ :< NeutPiIntro (y, _) body2, t):cs) = do
  var <- toVar' x
  simp $ (ctx, body1, subst [(y, var)] body2, t) : cs
simp'' ((ctx, _ :< NeutPiIntro (x, _) body1, e2, t):cs) = do
  var <- toVar' x
  appMeta <- newNameWith "meta"
  let app = appMeta :< NeutPiElim e2 var
  simp $ (ctx, body1, app, t) : cs
simp'' ((ctx, e1, e2@(_ :< NeutPiIntro _ _), t):cs) =
  simp $ (ctx, e2, e1, t) : cs
-- simp'' ((_, _ :< NeutSigma [], _ :< NeutSigma [], _):cs) = simp cs
-- simp'' ((ctx, i :< NeutSigma ((x, tx):xts), j :< NeutSigma ((y, ty):yts), univ):cs) = do
--   var <- toVar' x
--   cs' <- sConstraint [(y, var)] cs >>= simp
--   let sig' = subst [(y, var)] (j :< NeutSigma yts)
--   simp $
--     (ctx, tx, ty, univ) : (ctx ++ [x], i :< NeutSigma xts, sig', univ) : cs'
simp'' ((ctx, _ :< NeutSigma xts, _ :< NeutSigma yts, univ):cs)
  | length xts == length yts = do
    let (xs, txs) = unzip xts
    vs <- mapM toVar' xs
    let (ys, tys) = unzip yts
    let tys' = map (subst (zip ys vs)) tys
    newCs <- forM (zip txs tys') $ \(t1, t2) -> return (ctx, t1, t2, univ)
    simp $ newCs ++ cs
simp'' ((ctx, _ :< NeutSigmaIntro es1, _ :< NeutSigmaIntro es2, _ :< NeutSigma xts):cs)
  | length es1 == length es2 = do
    let (xs, ts) = unzip xts
    let ts' = map (subst $ zip xs es1) ts
    newCs <-
      forM (zip (zip es1 es2) ts') $ \((e1, e2), t') -> return (ctx, e1, e2, t')
    simp $ newCs ++ cs
simp'' ((ctx, _ :< NeutSigmaIntro es, e2, _ :< NeutSigma xts):cs)
  | length xts == length es = do
    prList <- projectionList e2 (map snd xts)
    let sub = zip (map fst xts) es
    let ts = map (subst sub . snd) xts
    newCs <-
      forM (zip3 es prList ts) $ \(e, ithProj, t) -> return (ctx, e, ithProj, t)
    simp $ newCs ++ cs
simp'' ((ctx, e1, e2@(_ :< NeutSigmaIntro es), t@(_ :< NeutSigma xts)):cs)
  | length xts == length es = simp $ (ctx, e2, e1, t) : cs
simp'' ((_, _ :< NeutIndex l1, _ :< NeutIndex l2, _):cs)
  | l1 == l2 = simp cs
simp'' ((_, _ :< NeutUniv i, _ :< NeutUniv j, _):cs) = do
  insUnivConstraintEnv i j
  simp cs
simp'' (c@(_, e1, _, _):cs)
  | Just _ <- headMeta' [] e1 = do
    cs' <- simp cs
    return $ c : cs'
simp'' (c@(_, _, e2, _):cs)
  | Just _ <- headMeta' [] e2 = do
    cs' <- simp cs
    return $ c : cs'
simp'' ((ctx, e1, e2, t):cs)
  | isReducible e1 = do
    e1' <- reduce e1
    simp $ (ctx, e1', e2, t) : cs
simp'' ((ctx, e1, e2, t):cs)
  | isReducible e2 = simp $ (ctx, e2, e1, t) : cs
simp'' (c@(ctx, e1, e2, t):cs) = do
  let mx = headMeta'' e1
  let my = headMeta'' e2
  sub <- gets substitution
  case (mx, my) of
    (Just x, _)
      | Just e <- lookup x sub -> simp $ (ctx, subst [(x, e)] e1, e2, t) : cs
    (_, Just y)
      | Just e <- lookup y sub -> simp $ (ctx, e1, subst [(y, e)] e2, t) : cs
    _ -> throwError $ "cannot simplify:\n" ++ Pr.ppShow c

categorize :: PreConstraint -> Constraint
categorize (ctx, _ :< NeutVar x, e2, t) = do
  let c = ConstraintBeta x e2
  Constraint ctx c t
categorize (ctx, e1, e2@(_ :< NeutVar _), t) = categorize (ctx, e2, e1, t)
categorize (ctx, e1, e2, t)
  | (_ :< NeutVar x, metaArgs1) <- toPiElimSeq e1
  , (_ :< NeutVar y, metaArgs2) <- toPiElimSeq e2
  , x == y
  , length metaArgs1 == length metaArgs2 = do
    let c = ConstraintDelta x (map snd metaArgs1) (map snd metaArgs2)
    Constraint ctx c t
categorize (ctx, e1, e2, t)
  | Just (x, args) <- headMeta [] e1
  , let (fvs, fmvs) = varAndHole e2
  , affineCheck args fvs && x `notElem` fmvs = do
    let c = ConstraintPattern x args e2
    Constraint ctx c t
categorize (ctx, e1, e2, t)
  | Just (x, args) <- headMeta [] e1
  , let (fvs, fmvs) = varAndHole e2
  , affineCheck args fvs && x `notElem` fmvs = categorize (ctx, e2, e1, t)
categorize (ctx, e1, e2, t)
  | Just (x, args) <- headMeta [] e1 = do
    let c = ConstraintQuasiPattern x args e2
    Constraint ctx c t
categorize (ctx, e1, e2, t)
  | Just _ <- headMeta [] e2 = categorize (ctx, e2, e1, t)
categorize (ctx, e1, e2, t)
  | Just (x, args1) <- headMeta' [] e1
  , Just (y, args2) <- headMeta' [] e2 = do
    let c = ConstraintFlexFlex x args1 y args2
    Constraint ctx c t
categorize (ctx, e1, e2, t)
  | Just (x, args) <- headMeta' [] e1 = do
    let c = ConstraintFlexRigid x args e2
    Constraint ctx c t
categorize (ctx, e1, e2, t)
  | Just _ <- headMeta' [] e2 = categorize (ctx, e2, e1, t)
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

isEqBranch :: [(IndexOrVar, Neut)] -> [(IndexOrVar, Neut)] -> WithEnv Bool
isEqBranch [] [] = return True
isEqBranch ((Right x1, e1):es1) ((Right x2, e2):es2) = do
  vx <- toVar' x1
  b1 <- isEq e1 $ subst [(x2, vx)] e2
  b2 <- isEqBranch es1 es2
  return $ b1 && b2
isEqBranch ((Left (IndexLabel x1), e1):es1) ((Left (IndexLabel x2), e2):es2)
  | x1 == x2 = do
    b1 <- isEq e1 e2
    b2 <- isEqBranch es1 es2
    return $ b1 && b2
isEqBranch ((Left (IndexInteger i1), e1):es1) ((Left (IndexInteger i2), e2):es2)
  | i1 == i2 = do
    b1 <- isEq e1 e2
    b2 <- isEqBranch es1 es2
    return $ b1 && b2
isEqBranch ((Left (IndexFloat i1), e1):es1) ((Left (IndexFloat i2), e2):es2)
  | i1 == i2 = do
    b1 <- isEq e1 e2
    b2 <- isEqBranch es1 es2
    return $ b1 && b2
isEqBranch ((Left IndexDefault, e1):es1) ((Left IndexDefault, e2):es2) = do
  b1 <- isEq e1 e2
  b2 <- isEqBranch es1 es2
  return $ b1 && b2
isEqBranch _ _ = return False

affineCheck :: [Identifier] -> [Identifier] -> Bool
affineCheck xs = affineCheck' xs xs

affineCheck' :: [Identifier] -> [Identifier] -> [Identifier] -> Bool
affineCheck' _ [] _ = True
affineCheck' xs (y:ys) fvs =
  if y `notElem` fvs
    then affineCheck' xs ys fvs
    else null (isLinear y xs) && affineCheck' xs ys fvs

projectionList :: Neut -> [Neut] -> WithEnv [Neut]
projectionList e ts = do
  xs <- forM ts $ \t -> newNameOfType t
  metaList <- mapM (const newName) xs
  let varList = map (\(meta, x) -> meta :< NeutVar x) $ zip metaList xs
  forM varList $ \x -> do
    meta <- newName
    return $ meta :< NeutSigmaElim e xs x

sConstraint :: Subst -> [PreConstraint] -> WithEnv [PreConstraint]
sConstraint s ctcs = do
  let (ctxList, cs, typeList) = split ctcs
  let (ts1, ts2) = unzip cs
  let ts1' = map (subst s) ts1
  let ts2' = map (subst s) ts2
  let typeList' = map (subst s) typeList
  return $ unsplit ctxList (zip ts1' ts2') typeList'

split :: [PreConstraint] -> ([[Identifier]], [(Neut, Neut)], [Neut])
split [] = ([], [], [])
split ((ctx, e1, e2, t):rest) = do
  let (ctxList, cs, typeList) = split rest
  (ctx : ctxList, (e1, e2) : cs, t : typeList)

unsplit :: [[Identifier]] -> [(Neut, Neut)] -> [Neut] -> [PreConstraint]
unsplit [] [] [] = []
unsplit (ctx:ctxList) ((e1, e2):cs) (t:typeList) =
  (ctx, e1, e2, t) : unsplit ctxList cs typeList
unsplit _ _ _ = error "Infer.unsplit: invalid arguments"

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
headMeta args (_ :< NeutHole x) = Just (x, args)
headMeta _ _ = Nothing

headMeta' :: [Neut] -> Neut -> Maybe (Identifier, [Neut])
headMeta' args (_ :< NeutPiElim e1 e2) = headMeta' (e2 : args) e1
headMeta' args (_ :< NeutHole x) = Just (x, args)
headMeta' _ _ = Nothing

headMeta'' :: Neut -> Maybe Identifier
headMeta'' (_ :< NeutVar x) = Just x
headMeta'' (_ :< NeutPiElim e1 _) = headMeta'' e1
headMeta'' (_ :< NeutIndexElim e _) = headMeta'' e
headMeta'' _ = Nothing
