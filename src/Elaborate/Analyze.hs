module Elaborate.Analyze
  ( analyze
  , simp
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
analyze cs = do
  cs' <- Q.fromList <$> simp cs
  modify (\e -> e {constraintQueue = cs' `Q.union` constraintQueue e})

simp :: [PreConstraint] -> WithEnv [EnrichedConstraint]
simp [] = return []
simp ((e1, e2):cs)
  | isReducible e1 = do
    me1' <- liftIO $ timeout 5000000 $ return $ reduceWeakTerm e1 -- 5 sec
    case me1' of
      Just e1' -> simp $ (e1', e2) : cs
      Nothing -> do
        let e1' = toDTerm e1
        let e2' = toDTerm e2
        throwError $ "cannot simplify [TIMEOUT]:\n" ++ Pr.ppShow (e1', e2')
simp ((e1, e2):cs)
  | isReducible e2 = simp $ (e2, e1) : cs
simp ((e1, e2):cs)
  | _ :< WeakTermPiElim s1 (_ :< WeakTermUpsilon f) es1 <- e1
  , _ :< WeakTermPiElim s2 (_ :< WeakTermUpsilon g) es2 <- e2
  , f == g
  , length es1 == length es2 = simp $ (s1, s2) : zip es1 es2 ++ cs
simp ((_ :< WeakTermUniv i, _ :< WeakTermUniv j):cs) = do
  insUnivConstraintEnv i j
  simp cs
simp ((_ :< WeakTermUpsilon x1, _ :< WeakTermUpsilon x2):cs)
  | x1 == x2 = simp cs
simp ((_ :< WeakTermEpsilon l1, _ :< WeakTermEpsilon l2):cs)
  | l1 == l2 = simp cs
simp ((_ :< WeakTermEpsilonIntro l1, _ :< WeakTermEpsilonIntro l2):cs)
  | l1 == l2 = simp cs
simp ((_ :< WeakTermPi s1 txs1, _ :< WeakTermPi s2 txs2):cs)
  | length txs1 == length txs2 = simpPiOrSigma s1 txs1 s2 txs2 cs
simp ((_ :< WeakTermPiIntro s1 txs1 body1, _ :< WeakTermPiIntro s2 txs2 body2):cs) = do
  h1 <- newNameWith "hole"
  h2 <- newNameWith "hole"
  simpPiOrSigma s1 (txs1 ++ [(body1, h1)]) s2 (txs2 ++ [(body2, h2)]) cs
simp ((_ :< WeakTermPiIntro s txs body1, e2):cs) = do
  let (_, xs) = unzip txs
  vs <- mapM toVar' xs
  appMeta <- newNameWith "meta"
  simp $ (body1, appMeta :< WeakTermPiElim s e2 vs) : cs
simp ((e1, e2@(_ :< WeakTermPiIntro {})):cs) = simp $ (e2, e1) : cs
simp ((_ :< WeakTermSigma s1 txs1, _ :< WeakTermSigma s2 txs2):cs)
  | length txs1 == length txs2 = simpPiOrSigma s1 txs1 s2 txs2 cs
simp ((_ :< WeakTermSigmaIntro s1 es1, _ :< WeakTermSigmaIntro s2 es2):cs)
  | length es1 == length es2 = simp $ (s1, s2) : zip es1 es2 ++ cs
simp ((_ :< WeakTermSigmaElim s txs e1 e2, e):cs) = do
  hs <- mapM (const newHole) txs
  sigmaIntro <- wrapType $ WeakTermSigmaIntro s hs
  let e2' = substWeakTerm (zip (map snd txs) hs) e2
  simp $ (e1, sigmaIntro) : (e2', e) : cs
simp ((e1, e2@(_ :< WeakTermSigmaElim {})):cs) = simp $ (e2, e1) : cs
simp ((_ :< WeakTermConst x, _ :< WeakTermConst y):cs)
  | x == y = simp cs
simp ((e1, e2):cs) = do
  let ms1 = asStuckedTerm e1
  let ms2 = asStuckedTerm e2
  case (ms1, ms2) of
    (Just (StuckHole m, _), _) -> do
      cs' <- simp cs
      return $ Enriched (e1, e2) [m] (ConstraintImmediate m e2) : cs'
    (_, Just (StuckHole _, _)) -> simp $ (e2, e1) : cs
    (Just (StuckPiElimStrict s1 m1 exs1, _), _)
      | (es1, xs1) <- unzip exs1
      , isSolvable e2 m1 xs1 -> do
        cs' <- simp cs
        return $ Enriched (e1, e2) [m1] (ConstraintPattern s1 m1 es1 e2) : cs'
    (_, Just (StuckPiElimStrict _ m2 exs2, _))
      | isSolvable e1 m2 (map snd exs2) -> simp $ (e2, e1) : cs
    (Just (StuckPiElimStrict s1 m1 exs1, _), _) -> do
      cs' <- simp cs
      return $
        Enriched (e1, e2) [m1] (ConstraintQuasiPattern s1 m1 (map fst exs1) e2) :
        cs'
    (_, Just (StuckPiElimStrict {}, _)) -> simp $ (e2, e1) : cs
    (Just (StuckPiElim s1 m1 es1, _), Nothing) -> do
      cs' <- simp cs
      let c = Enriched (e1, e2) [m1] $ ConstraintFlexRigid s1 m1 es1 e2
      return $ c : cs'
    (Nothing, Just (StuckPiElim {}, _)) -> simp $ (e2, e1) : cs
    (Just (StuckPiElim s1 m1 es1, _), _) -> do
      cs' <- simp cs
      let c = Enriched (e1, e2) [m1] $ ConstraintFlexFlex s1 m1 es1 e2
      return $ c : cs'
    (_, Just (StuckPiElim {}, _)) -> simp $ (e2, e1) : cs
    (Just (StuckOther, m1), _) -> do
      cs' <- simp cs
      let c = Enriched (e1, e2) [m1] ConstraintOther
      return $ c : cs'
    (_, Just (StuckOther, _)) -> simp $ (e2, e1) : cs
    _ -> throwError $ "cannot simplify:\n" ++ Pr.ppShow (toDTerm e1, toDTerm e2)

simpPiOrSigma ::
     WeakTerm
  -> [(WeakTerm, Identifier)]
  -> WeakTerm
  -> [(WeakTerm, Identifier)]
  -> [(WeakTerm, WeakTerm)]
  -> WithEnv [EnrichedConstraint]
simpPiOrSigma s1 txs1 s2 txs2 cs = do
  let (ts1, xs1) = unzip txs1
  vs1 <- mapM toVar' xs1
  let (ts2, xs2) = unzip txs2
  let ts2' = map (substWeakTerm (zip xs2 vs1)) ts2
  simp $ (s1, s2) : zip ts1 ts2' ++ cs

data Stuck
  = StuckHole Identifier
  | StuckPiElim WeakSortal
                Identifier
                [WeakTerm]
  | StuckPiElimStrict WeakSortal
                      Identifier
                      [(WeakTerm, Identifier)]
  | StuckOther

asStuckedTerm :: WeakTerm -> Maybe (Stuck, Identifier)
asStuckedTerm (_ :< WeakTermHole m) = Just (StuckHole m, m)
asStuckedTerm (_ :< WeakTermPiElim s (_ :< WeakTermHole x) es) =
  case mapM interpretAsUpsilon es of
    Nothing -> Just (StuckPiElim s x es, x)
    Just xs -> Just (StuckPiElimStrict s x (zip es xs), x)
asStuckedTerm (_ :< WeakTermEpsilonElim _ e _)
  | Just m <- obtainStuckReason e = Just (StuckOther, m)
asStuckedTerm _ = Nothing

obtainStuckReason :: WeakTerm -> Maybe Identifier
obtainStuckReason (_ :< WeakTermHole x)             = Just x
obtainStuckReason (_ :< WeakTermPiElim _ e _)       = obtainStuckReason e
obtainStuckReason (_ :< WeakTermSigmaElim _ _ e1 _) = obtainStuckReason e1
obtainStuckReason (_ :< WeakTermEpsilonElim _ e _)  = obtainStuckReason e
obtainStuckReason _                                 = Nothing

isSolvable :: WeakTerm -> Identifier -> [Identifier] -> Bool
isSolvable e x xs = do
  let (fvs, fmvs) = varAndHole e
  affineCheck xs fvs && x `notElem` fmvs

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

bindFormalArgs :: WeakSortal -> [Identifier] -> WeakTerm -> WithEnv WeakTerm
bindFormalArgs s xs e = do
  ts <- mapM (const newHole) xs
  meta <- newNameWith "meta"
  return $ meta :< WeakTermPiIntro s (zip ts xs) e

interpretAsUpsilon :: WeakTerm -> Maybe Identifier
interpretAsUpsilon (_ :< WeakTermUpsilon x) = Just x
interpretAsUpsilon _                        = Nothing
