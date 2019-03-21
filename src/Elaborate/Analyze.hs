module Elaborate.Analyze
  ( simp
  , analyze
  , categorize
  , updateQueue
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
  | Just (f, es1) <- headMeta1 [] e1
  , Just (g, es2) <- headMeta1 [] e2
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
simp'' ((_, _ :< NeutSigma [], _ :< NeutSigma [], _):cs) = simp cs
simp'' ((ctx, i :< NeutSigma ((x, tx):xts), j :< NeutSigma ((y, ty):yts), univ):cs) = do
  var <- toVar' x
  cs' <- sConstraint [(y, var)] cs >>= simp
  let sig' = subst [(y, var)] (j :< NeutSigma yts)
  simp $
    (ctx, tx, ty, univ) : (ctx ++ [x], i :< NeutSigma xts, sig', univ) : cs'
simp'' ((ctx, _ :< NeutSigmaIntro es1, _ :< NeutSigmaIntro es2, _ :< NeutSigma xts):cs)
  | length es1 == length es2 = do
    let (_, ts) = unzip xts
    let sub = zip (map fst xts) es1
    let ts' = map (subst sub) ts
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
    e1' <- reduce' e1
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

-- update the `constraintQueue` by `q`, updating its content using current substitution
updateQueue :: Q.MinQueue EnrichedConstraint -> WithEnv ()
updateQueue q = do
  modify (\e -> e {constraintQueue = Q.empty})
  sub <- gets substitution
  updateQueue' sub q

updateQueue' :: Subst -> Q.MinQueue EnrichedConstraint -> WithEnv ()
updateQueue' sub q =
  case Q.getMin q of
    Nothing -> return ()
    Just (Enriched (ctx, e1, e2, t) _) -> do
      analyze [(ctx, subst sub e1, subst sub e2, t)]
      updateQueue' sub $ Q.deleteMin q
