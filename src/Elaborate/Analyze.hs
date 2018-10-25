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

import Data.Maybe

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
      e' <- nonRecReduce e
      ans <- bindFormalArgs' args e'
      modify (\e -> e {substitution = compose [(hole, ans)] (substitution e)})
      q <- gets constraintQueue
      updateQueue q
    _ -> do
      let ec = Enriched c $ categorize c
      modify (\e -> e {constraintQueue = Q.insert ec $ constraintQueue e})

simp :: [PreConstraint] -> WithEnv [PreConstraint]
simp [] = return []
simp ((ctx, e1, e2, t):cs)
  | isNonRecReducible e1 = do
    e1' <- nonRecReduce e1
    simp $ (ctx, e1', e2, t) : cs
simp ((ctx, e1, e2, t):cs)
  | isNonRecReducible e2 = simp $ (ctx, e2, e1, t) : cs
simp ((_, _ :< NeutVar s1, _ :< NeutVar s2, _):cs)
  | s1 == s2 = simp cs
simp ((ctx, _ :< NeutVar s1, e2, t):cs) = do
  me <- insDef s1 e2
  case me of
    Nothing -> simp cs
    Just e -> simp $ (ctx, e, e2, t) : cs
simp ((ctx, e1, v@(_ :< NeutVar _), t):cs) = simp $ (ctx, v, e1, t) : cs
simp ((ctx, _ :< NeutPi (x, tdom1) tcod1, _ :< NeutPi (y, tdom2) tcod2, univ):cs) = do
  var <- toVar' x
  cs' <- sConstraint [(y, var)] cs >>= simp
  simp $
    (ctx, tdom1, tdom2, univ) :
    (ctx ++ [x], tcod1, subst [(y, var)] tcod2, univ) : cs'
simp ((ctx, _ :< NeutPiIntro (x, _) body1, _ :< NeutPiIntro (y, _) body2, t):cs) = do
  var <- toVar' x
  simp $ (ctx, body1, subst [(y, var)] body2, t) : cs
simp ((ctx, _ :< NeutPiIntro (x, _) body1, e2, t):cs) = do
  var <- toVar' x
  appMeta <- newNameWith "meta"
  let app = appMeta :< NeutPiElim e2 var
  simp $ (ctx, body1, app, t) : cs
simp ((ctx, e1, e2@(_ :< NeutPiIntro _ _), t):cs) = simp $ (ctx, e2, e1, t) : cs
simp ((ctx, _ :< NeutSigma [(x, tdom1)] tcod1, _ :< NeutSigma [(y, tdom2)] tcod2, univ):cs) = do
  var <- toVar' x
  cs' <- sConstraint [(y, var)] cs >>= simp
  simp $
    (ctx, tdom1, tdom2, univ) :
    (ctx ++ [x], tcod1, subst [(y, var)] tcod2, univ) : cs'
simp ((ctx, i :< NeutSigma ((x, tdom1):xts) tcod1, j :< NeutSigma ((y, tdom2):yts) tcod2, univ):cs) = do
  let sig1 = i :< NeutSigma [(x, tdom1)] (i :< NeutSigma xts tcod1)
  let sig2 = j :< NeutSigma [(y, tdom2)] (j :< NeutSigma yts tcod2)
  simp ((ctx, sig1, sig2, univ) : cs)
simp ((ctx, _ :< NeutSigmaIntro es1, _ :< NeutSigmaIntro es2, _ :< NeutSigma xts t):cs)
  | length es1 == length es2 = do
    let ts = map snd xts ++ [t]
    let sub = zip (map fst xts) es1
    let ts' = map (subst sub) ts
    newCs <-
      forM (zip (zip es1 es2) ts') $ \((e1, e2), t') -> return (ctx, e1, e2, t')
    simp $ newCs ++ cs
simp ((ctx, _ :< NeutSigmaIntro es, e2, _ :< NeutSigma xts t):cs)
  | length xts + 1 == length es = do
    prList <- projectionList e2 (xts, t)
    let sub = zip (map fst xts) es
    let ts = map (subst sub) $ map snd xts ++ [t]
    newCs <-
      forM (zip3 es prList ts) $ \(e, ithProj, t) -> return (ctx, e, ithProj, t)
    simp $ newCs ++ cs
simp ((ctx, e1, e2@(_ :< NeutSigmaIntro es), t@(_ :< NeutSigma xts _)):cs)
  | length xts + 1 == length es = simp $ (ctx, e2, e1, t) : cs
simp ((ctx, _ :< NeutBox t1, _ :< NeutBox t2, univ):cs) =
  simp $ (ctx, t1, t2, univ) : cs
simp ((ctx, _ :< NeutBoxIntro e1, _ :< NeutBoxIntro e2, _ :< NeutBox t):cs) =
  simp $ (ctx, e1, e2, t) : cs
simp ((ctx, _ :< NeutBoxElim e1, _ :< NeutBoxElim e2, t):cs) = do
  meta <- newNameWith "meta"
  simp $ (ctx, e1, e2, meta :< NeutBox t) : cs
simp ((ctx, _ :< NeutConst t1, _ :< NeutConst t2, univ):cs) =
  simp $ (ctx, t1, t2, univ) : cs
simp ((_, _ :< NeutIndex l1, _ :< NeutIndex l2, _):cs)
  | l1 == l2 = simp cs
simp ((_, _ :< NeutUniv i, _ :< NeutUniv j, _):cs) = do
  insUnivConstraintEnv i j
  simp cs
simp (c@(_, e1, _, _):cs)
  | Just _ <- headMeta' [] e1 = do
    cs' <- simp cs
    return $ c : cs'
simp (c@(_, _, e2, _):cs)
  | Just _ <- headMeta' [] e2 = do
    cs' <- simp cs
    return $ c : cs'
simp (c@(_, e1, e2, _):cs) = do
  b <- isEq e1 e2
  if b
    then simp cs
    else throwError $ "cannot simplify:\n" ++ Pr.ppShow c

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
-- projectionList :: Neut -> ([(Identifier, Neut)], Neut) -> WithEnv [Neut]
-- projectionList e (xts, t) = do
--   xiList <- forM (map snd xts ++ [t]) $ \t -> newNameOfType t
--   metaList <- mapM (const newName) xiList
--   let varList = map (\(m, x) -> m :< NeutVar x) $ zip metaList xiList
--   forM varList $ \v -> do
--     meta <- newName
--     return $ meta :< NeutSigmaElim e xiList v
