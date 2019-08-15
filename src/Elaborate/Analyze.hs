module Elaborate.Analyze
  ( analyze
  , simp
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
analyze cs = do
  cs' <- Q.fromList <$> simp cs
  modify (\e -> e {constraintQueue = cs' `Q.union` constraintQueue e})

simp :: [PreConstraint] -> WithEnv [EnrichedConstraint]
simp [] = return []
simp ((e1, e2):cs)
  | isReducible e1 = do
    me1' <- reduceWeakTerm e1 >>= \e1' -> liftIO $ timeout 5000000 $ return e1'
    case me1' of
      Just e1' -> simp $ (e1', e2) : cs
      Nothing ->
        throwError $ "cannot simplify [TIMEOUT]:\n" ++ Pr.ppShow (e1, e2)
simp ((e1, e2):cs)
  | isReducible e2 = simp $ (e2, e1) : cs
simp ((_ :< WeakTermTau, _ :< WeakTermTau):cs) = simp cs
simp ((_ :< WeakTermTheta x, _ :< WeakTermTheta y):cs)
  | x == y = simp cs
simp ((_ :< WeakTermUpsilon x1, _ :< WeakTermUpsilon x2):cs)
  | x1 == x2 = simp cs
simp ((_ :< WeakTermEpsilon l1, _ :< WeakTermEpsilon l2):cs)
  | l1 == l2 = simp cs
simp ((_ :< WeakTermEpsilonIntro l1, _ :< WeakTermEpsilonIntro l2):cs)
  | l1 == l2 = simp cs
simp ((_ :< WeakTermPi xts1, _ :< WeakTermPi xts2):cs)
  | length xts1 == length xts2 = simpPiOrSigma xts1 xts2 cs
simp ((_ :< WeakTermPiIntro xts1 body1, _ :< WeakTermPiIntro xts2 body2):cs) = do
  h1 <- newNameWith "hole"
  h2 <- newNameWith "hole"
  simpPiOrSigma (xts1 ++ [(h1, body1)]) (xts2 ++ [(h2, body2)]) cs
simp ((_ :< WeakTermPiIntro xts body1, e2):cs) = do
  let (xs, _) = unzip xts
  vs <- mapM toVar xs
  appMeta <- newMeta
  simp $ (body1, appMeta :< WeakTermPiElim e2 vs) : cs
simp ((e1, e2@(_ :< WeakTermPiIntro {})):cs) = simp $ (e2, e1) : cs
simp ((_ :< WeakTermSigma xts1, _ :< WeakTermSigma xts2):cs)
  | length xts1 == length xts2 = simpPiOrSigma xts1 xts2 cs
simp ((_ :< WeakTermSigmaIntro es1, _ :< WeakTermSigmaIntro es2):cs)
  | length es1 == length es2 = simp $ zip es1 es2 ++ cs
simp ((e1, e2):cs)
  | _ :< WeakTermPiElim (_ :< WeakTermUpsilon f) es1 <- e1
  , _ :< WeakTermPiElim (_ :< WeakTermUpsilon g) es2 <- e2
  , f == g
  , length es1 == length es2 = simp $ zip es1 es2 ++ cs
simp ((e1, e2):cs) = do
  let ms1 = asStuckedTerm e1
  let ms2 = asStuckedTerm e2
  case (ms1, ms2) of
    (Just (StuckHole m), _) -> do
      cs' <- simp cs
      return $ Enriched (e1, e2) [m] (ConstraintImmediate m e2) : cs'
    (_, Just (StuckHole _)) -> simp $ (e2, e1) : cs
    (Just (StuckPiElimStrict m1 exs1), _)
      | all (isSolvable e2 m1) (map (map snd) exs1) -> do
        cs' <- simp cs
        let es1 = map (map fst) exs1
        return $ Enriched (e1, e2) [m1] (ConstraintPattern m1 es1 e2) : cs'
    (_, Just (StuckPiElimStrict m2 exs2))
      | all (isSolvable e1 m2) (map (map snd) exs2) -> simp $ (e2, e1) : cs
    (Just (StuckPiElimStrict m1 exs1), _) -> do
      cs' <- simp cs
      let es1 = map (map fst) exs1
      return $ Enriched (e1, e2) [m1] (ConstraintQuasiPattern m1 es1 e2) : cs'
    (_, Just StuckPiElimStrict {}) -> simp $ (e2, e1) : cs
    (Just (StuckPiElim m1 ies1), Nothing) -> do
      cs' <- simp cs
      let c = Enriched (e1, e2) [m1] $ ConstraintFlexRigid m1 ies1 e2
      return $ c : cs'
    (Nothing, Just StuckPiElim {}) -> simp $ (e2, e1) : cs
    (Just (StuckPiElim m1 ies1), _) -> do
      cs' <- simp cs
      let c = Enriched (e1, e2) [m1] $ ConstraintFlexFlex m1 ies1 e2
      return $ c : cs'
    (_, Just StuckPiElim {}) -> simp $ (e2, e1) : cs
    (Just (StuckOther m1), _) -> do
      cs' <- simp cs
      let c = Enriched (e1, e2) [m1] ConstraintOther
      return $ c : cs'
    (_, Just (StuckOther _)) -> simp $ (e2, e1) : cs
    _ -> throwError $ "cannot simplify:\n" ++ Pr.ppShow (e1, e2)

simpPiOrSigma ::
     [(Identifier, WeakTerm)]
  -> [(Identifier, WeakTerm)]
  -> [(WeakTerm, WeakTerm)]
  -> WithEnv [EnrichedConstraint]
simpPiOrSigma xts1 xts2 cs = do
  let (xs1, ts1) = unzip xts1
  vs1 <- mapM toVar xs1
  let (xs2, ts2) = unzip xts2
  let ts2' = map (substWeakTerm (zip xs2 vs1)) ts2
  simp $ zip ts1 ts2' ++ cs

data Stuck
  = StuckHole Hole
  | StuckPiElim Hole
                [[WeakTerm]]
  | StuckPiElimStrict Hole
                      [[(WeakTerm, Identifier)]]
  | StuckOther Hole

asStuckedTerm :: WeakTerm -> Maybe Stuck
asStuckedTerm (_ :< WeakTermPiElim e es)
  | Just xs <- mapM interpretAsUpsilon es =
    case asStuckedTerm e of
      Just (StuckHole m) -> Just $ StuckPiElimStrict m [zip es xs]
      Just (StuckPiElim m iess) -> Just $ StuckPiElim m (iess ++ [es])
      Just (StuckPiElimStrict m iexss) ->
        Just $ StuckPiElimStrict m $ iexss ++ [zip es xs]
      Just (StuckOther m) -> Just $ StuckOther m
      Nothing -> Nothing
asStuckedTerm (_ :< WeakTermPiElim e es) =
  case asStuckedTerm e of
    Just (StuckHole m) -> Just $ StuckPiElim m [es]
    Just (StuckPiElim m iess) -> Just $ StuckPiElim m $ iess ++ [es]
    Just (StuckPiElimStrict m exss) -> do
      let ess = map (map fst) exss
      Just $ StuckPiElim m $ ess ++ [es]
    Just (StuckOther m) -> Just $ StuckOther m
    Nothing -> Nothing
asStuckedTerm (_ :< WeakTermZeta m) = Just $ StuckHole m
asStuckedTerm e
  | Just m <- obtainStuckReason e = Just $ StuckOther m
asStuckedTerm _ = Nothing

obtainStuckReason :: WeakTerm -> Maybe Hole
obtainStuckReason (_ :< WeakTermEpsilonElim _ e _) = obtainStuckReason e
obtainStuckReason (_ :< WeakTermPiElim e _)        = obtainStuckReason e
obtainStuckReason (_ :< WeakTermSigmaElim _ e1 _)  = obtainStuckReason e1
obtainStuckReason (_ :< WeakTermZeta x)            = Just x
obtainStuckReason _                                = Nothing

isSolvable :: WeakTerm -> Identifier -> [Identifier] -> Bool
isSolvable e x xs = do
  let (fvs, fmvs) = varWeakTerm e
  affineCheck xs fvs && x `notElem` fmvs

toVar :: Identifier -> WithEnv WeakTerm
toVar x = do
  meta <- newMeta
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

interpretAsUpsilon :: WeakTerm -> Maybe Identifier
interpretAsUpsilon (_ :< WeakTermUpsilon x) = Just x
interpretAsUpsilon _                        = Nothing
