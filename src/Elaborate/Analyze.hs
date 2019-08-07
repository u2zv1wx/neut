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
    me1' <- liftToWithEnv (timeout 5000000) $ reduceWeakTerm e1 -- 5 sec
    case me1' of
      Just e1' -> simp $ (e1', e2) : cs
      Nothing ->
        throwError $ "cannot simplify [TIMEOUT]:\n" ++ Pr.ppShow (e1, e2)
simp ((e1, e2):cs)
  | isReducible e2 = simp $ (e2, e1) : cs
simp ((_ :< WeakTermUniv i, _ :< WeakTermUniv j):cs) = do
  simpLevel i j
  simp cs
simp ((_ :< WeakTermUpsilon x1, _ :< WeakTermUpsilon x2):cs)
  | x1 == x2 = simp cs
simp ((_ :< WeakTermEpsilon l1, _ :< WeakTermEpsilon l2):cs)
  | l1 == l2 = simp cs
simp ((_ :< WeakTermEpsilonIntro l1, _ :< WeakTermEpsilonIntro l2):cs)
  | l1 == l2 = simp cs
simp ((_ :< WeakTermPi i1 xts1, _ :< WeakTermPi i2 xts2):cs)
  | length xts1 == length xts2 = do
    simpLevel i1 i2
    simpPiOrSigma xts1 xts2 cs
simp ((_ :< WeakTermPiIntro i1 xts1 body1, _ :< WeakTermPiIntro i2 xts2 body2):cs) = do
  simpLevel i1 i2
  h1 <- newNameWith "hole"
  h2 <- newNameWith "hole"
  simpPiOrSigma (xts1 ++ [(h1, body1)]) (xts2 ++ [(h2, body2)]) cs
simp ((_ :< WeakTermPiIntro i1 xts body1, e2):cs) = do
  let (xs, _) = unzip xts
  vs <- mapM toVar' xs
  appMeta <- newNameWith "meta"
  simp $ (body1, appMeta :< WeakTermPiElim i1 e2 vs) : cs
simp ((e1, e2@(_ :< WeakTermPiIntro {})):cs) = simp $ (e2, e1) : cs
simp ((_ :< WeakTermSigma i1 xts1, _ :< WeakTermSigma i2 xts2):cs)
  | length xts1 == length xts2 = do
    simpLevel i1 i2
    simpPiOrSigma xts1 xts2 cs
simp ((_ :< WeakTermSigmaIntro i1 es1, _ :< WeakTermSigmaIntro i2 es2):cs)
  | length es1 == length es2 = do
    simpLevel i1 i2
    simp $ zip es1 es2 ++ cs
simp ((_ :< WeakTermTau i1 t1, _ :< WeakTermTau i2 t2):cs) = do
  simpLevel i1 i2
  simp $ (t1, t2) : cs
simp ((_ :< WeakTermTauIntro i1 e1, _ :< WeakTermTauIntro i2 e2):cs) = do
  simpLevel i1 i2
  simp $ (e1, e2) : cs
simp ((_ :< WeakTermTheta t1, _ :< WeakTermTheta t2):cs) = simp $ (t1, t2) : cs
simp ((_ :< WeakTermThetaIntro e1, _ :< WeakTermThetaIntro e2):cs) =
  simp $ (e1, e2) : cs
simp ((_ :< WeakTermConst x, _ :< WeakTermConst y):cs)
  | x == y = simp cs
simp ((e1, e2):cs)
  | _ :< WeakTermPiElim i1 (_ :< WeakTermUpsilon f) es1 <- e1
  , _ :< WeakTermPiElim i2 (_ :< WeakTermUpsilon g) es2 <- e2
  , f == g
  , length es1 == length es2 = do
    simpLevel i1 i2
    simp $ zip es1 es2 ++ cs
simp ((e1, e2):cs) = do
  let ms1 = asStuckedTerm e1
  let ms2 = asStuckedTerm e2
  case (ms1, ms2) of
    (Just (StuckHole m, _), _) -> do
      cs' <- simp cs
      return $ Enriched (e1, e2) [m] (ConstraintImmediate m e2) : cs'
    (_, Just (StuckHole _, _)) -> simp $ (e2, e1) : cs
    (Just (StuckPiElimStrict i m1 exs1, _), _)
      | (es1, xs1) <- unzip exs1
      , isSolvable e2 (fst m1) xs1 -> do
        cs' <- simp cs
        return $ Enriched (e1, e2) [m1] (ConstraintPattern i m1 es1 e2) : cs'
    (_, Just (StuckPiElimStrict _ m2 exs2, _))
      | isSolvable e1 (fst m2) (map snd exs2) -> simp $ (e2, e1) : cs
    (Just (StuckPiElimStrict i m1 exs1, _), _) -> do
      cs' <- simp cs
      return $
        Enriched (e1, e2) [m1] (ConstraintQuasiPattern i m1 (map fst exs1) e2) :
        cs'
    (_, Just (StuckPiElimStrict {}, _)) -> simp $ (e2, e1) : cs
    (Just (StuckPiElim i m1 es1, _), Nothing) -> do
      cs' <- simp cs
      let c = Enriched (e1, e2) [m1] $ ConstraintFlexRigid i m1 es1 e2
      return $ c : cs'
    (Nothing, Just (StuckPiElim {}, _)) -> simp $ (e2, e1) : cs
    (Just (StuckPiElim i m1 es1, _), _) -> do
      cs' <- simp cs
      let c = Enriched (e1, e2) [m1] $ ConstraintFlexFlex i m1 es1 e2
      return $ c : cs'
    (_, Just (StuckPiElim {}, _)) -> simp $ (e2, e1) : cs
    (Just (StuckOther, m1), _) -> do
      cs' <- simp cs
      let c = Enriched (e1, e2) [m1] ConstraintOther
      return $ c : cs'
    (_, Just (StuckOther, _)) -> simp $ (e2, e1) : cs
    _ -> throwError $ "cannot simplify:\n" ++ Pr.ppShow (e1, e2)

-- FIXME: ここのsimpは実際には結構まとまった量の処理になる
simpLevel :: WeakLevel -> WeakLevel -> WithEnv ()
simpLevel (WeakLevelInt i1) (WeakLevelInt i2)
  | i1 == i2 = return ()
simpLevel WeakLevelInfinity WeakLevelInfinity = return ()
simpLevel (WeakLevelHole (h, i)) l = do
  let l' = WeakLevelAdd l i
  modify (\env -> env {levelEnv = composeWeakLevel [(h, l')] (levelEnv env)})
simpLevel l (WeakLevelHole h) = simpLevel (WeakLevelHole h) l
simpLevel l1 l2 =
  throwError $ "LevelError: cannot simplify: " ++ show l1 ++ " with " ++ show l2

simpPiOrSigma ::
     [(Identifier, WeakTerm)]
  -> [(Identifier, WeakTerm)]
  -> [(WeakTerm, WeakTerm)]
  -> WithEnv [EnrichedConstraint]
simpPiOrSigma xts1 xts2 cs = do
  let (xs1, ts1) = unzip xts1
  vs1 <- mapM toVar' xs1
  let (xs2, ts2) = unzip xts2
  let ts2' = map (substWeakTerm (zip xs2 vs1)) ts2
  simp $ zip ts1 ts2' ++ cs

data Stuck
  = StuckHole Hole
  | StuckPiElim WeakLevel
                Hole
                [WeakTerm]
  | StuckPiElimStrict WeakLevel
                      Hole
                      [(WeakTerm, Identifier)]
  | StuckOther

asStuckedTerm :: WeakTerm -> Maybe (Stuck, Hole)
asStuckedTerm (_ :< WeakTermHole m) = Just (StuckHole m, m)
asStuckedTerm (_ :< WeakTermPiElim i (_ :< WeakTermHole x) es) =
  case mapM interpretAsUpsilon es of
    Nothing -> Just (StuckPiElim i x es, x)
    Just xs -> Just (StuckPiElimStrict i x (zip es xs), x)
asStuckedTerm (_ :< WeakTermEpsilonElim _ e _)
  | Just m <- obtainStuckReason e = Just (StuckOther, m)
asStuckedTerm _ = Nothing

obtainStuckReason :: WeakTerm -> Maybe Hole
obtainStuckReason (_ :< WeakTermEpsilonElim _ e _)  = obtainStuckReason e
obtainStuckReason (_ :< WeakTermPiElim _ e _)       = obtainStuckReason e
obtainStuckReason (_ :< WeakTermSigmaElim _ _ e1 _) = obtainStuckReason e1
obtainStuckReason (_ :< WeakTermTauElim _ e)        = obtainStuckReason e
obtainStuckReason (_ :< WeakTermThetaElim e _)      = obtainStuckReason e
obtainStuckReason (_ :< WeakTermHole x)             = Just x
obtainStuckReason _                                 = Nothing

isSolvable :: WeakTerm -> Identifier -> [Identifier] -> Bool
isSolvable e x xs = do
  let (fvs, fmvs) = varAndHole e
  affineCheck xs fvs && x `notElem` map fst fmvs

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

interpretAsUpsilon :: WeakTerm -> Maybe Identifier
interpretAsUpsilon (_ :< WeakTermUpsilon x) = Just x
interpretAsUpsilon _                        = Nothing
