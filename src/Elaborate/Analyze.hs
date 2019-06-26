module Elaborate.Analyze
  ( analyzePlus
  , analyze
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

analyzePlus :: [PreConstraint] -> WithEnv ()
analyzePlus cs = do
  cs' <- Q.fromList <$> analyze cs
  modify (\e -> e {constraintQueue = cs' `Q.union` constraintQueue e})

analyze :: [PreConstraint] -> WithEnv [EnrichedConstraint]
analyze [] = return []
analyze ((e1, e2):cs)
  | isReducible e1 = do
    me1' <- liftIO $ timeout 5000000 $ return $ reduceWeakTerm e1 -- 5 sec
    case me1' of
      Just e1' -> analyze $ (e1', e2) : cs
      Nothing -> do
        let e1' = toDTerm e1
        let e2' = toDTerm e2
        throwError $ "cannot analyzelify [TIMEOUT]:\n" ++ Pr.ppShow (e1', e2')
analyze ((e1, e2):cs)
  | isReducible e2 = analyze $ (e2, e1) : cs
analyze ((e1, e2):cs)
  | _ :< WeakTermPiElim _ (_ :< WeakTermUpsilon f) es1 <- e1
  , _ :< WeakTermPiElim _ (_ :< WeakTermUpsilon g) es2 <- e2
  , f == g
  , length es1 == length es2 = analyze $ zip es1 es2 ++ cs
analyze ((_ :< WeakTermUniv i, _ :< WeakTermUniv j):cs) = do
  insUnivConstraintEnv i j
  analyze cs
analyze ((_ :< WeakTermEpsilon l1, _ :< WeakTermEpsilon l2):cs) = do
  analyzeEpsilon l1 l2
  analyze cs
analyze ((_ :< WeakTermPi s1 txs1, _ :< WeakTermPi s2 txs2):cs)
  | length txs1 == length txs2 = analyzePiOrSigma s1 txs1 s2 txs2 cs
analyze ((_ :< WeakTermPiIntro s1 txs1 body1, _ :< WeakTermPiIntro s2 txs2 body2):cs) = do
  h1 <- newNameWith "hole"
  h2 <- newNameWith "hole"
  analyzePiOrSigma s1 (txs1 ++ [(body1, h1)]) s2 (txs2 ++ [(body2, h2)]) cs
analyze ((_ :< WeakTermPiIntro s txs body1, e2):cs) = do
  let (_, xs) = unzip txs
  vs <- mapM toVar' xs
  appMeta <- newNameWith "meta"
  analyze $ (body1, appMeta :< WeakTermPiElim s e2 vs) : cs
analyze ((e1, e2@(_ :< WeakTermPiIntro {})):cs) = analyze $ (e2, e1) : cs
analyze ((_ :< WeakTermSigma s1 txs1, _ :< WeakTermSigma s2 txs2):cs)
  | length txs1 == length txs2 = analyzePiOrSigma s1 txs1 s2 txs2 cs
analyze ((_ :< WeakTermSigmaIntro s1 es1, _ :< WeakTermSigmaIntro s2 es2):cs)
  | length es1 == length es2 = analyze $ (s1, s2) : zip es1 es2 ++ cs
analyze ((_ :< WeakTermSigmaIntro s1 es, e2):cs) = do
  prList <- projectionList s1 e2 (length es)
  analyze $ zip es prList ++ cs
analyze ((e1, e2@(_ :< WeakTermSigmaIntro _ _)):cs) = analyze $ (e2, e1) : cs
analyze ((_ :< WeakTermConst x, _ :< WeakTermConst y):cs)
  | x == y = analyze cs
analyze ((e1, e2):cs) = do
  let ms1 = asStuckedTerm e1
  let ms2 = asStuckedTerm e2
  case (ms1, ms2) of
    (Just (StuckPiElimStrict s1 m1 xs1, _), _)
      | isSolvable e2 m1 xs1 -> do
        ans <- bindFormalArgs s1 xs1 e2
        let newSub = [(m1, ans)]
        modify (\env -> env {substitution = compose newSub (substitution env)})
        analyze cs
    (_, Just (StuckPiElimStrict _ m2 xs2, _))
      | isSolvable e1 m2 xs2 -> analyze $ (e2, e1) : cs
    (Just (StuckPiElimStrict s1 m1 xs1, _), _) -> do
      cs' <- analyze cs
      return $ Enriched (e1, e2) (ConstraintQuasiPattern s1 m1 xs1 e2) : cs'
    (_, Just (StuckPiElimStrict {}, _)) -> analyze $ (e2, e1) : cs
    (Just (StuckPiElim s1 x1 es1, _), Nothing) -> do
      cs' <- analyze cs
      let c = Enriched (e1, e2) $ ConstraintFlexRigid s1 x1 es1 e2
      return $ c : cs'
    (Nothing, Just (StuckPiElim {}, _)) -> analyze $ (e2, e1) : cs
    (Just (_, m1), Just (_, m2)) -> do
      cs' <- analyze cs
      let c = Enriched (e1, e2) $ ConstraintOther [m1, m2]
      return $ c : cs'
    _ ->
      throwError $ "cannot analyzelify:\n" ++ Pr.ppShow (toDTerm e1, toDTerm e2)

analyzeEpsilon :: WeakEpsilon -> WeakEpsilon -> WithEnv ()
analyzeEpsilon (WeakEpsilonIdentifier x) (WeakEpsilonIdentifier y)
  | x == y = return ()
analyzeEpsilon (WeakEpsilonIdentifier _) (WeakEpsilonHole _) = undefined
analyzeEpsilon (WeakEpsilonHole _) (WeakEpsilonIdentifier _) = undefined
analyzeEpsilon _ _ = throwError "cannot analyzelify (analyzeEpsilon)"

analyzePiOrSigma ::
     WeakTerm
  -> [(WeakTerm, Identifier)]
  -> WeakTerm
  -> [(WeakTerm, Identifier)]
  -> [(WeakTerm, WeakTerm)]
  -> WithEnv [EnrichedConstraint]
analyzePiOrSigma s1 txs1 s2 txs2 cs = do
  let (ts1, xs1) = unzip txs1
  vs1 <- mapM toVar' xs1
  let (ts2, xs2) = unzip txs2
  let ts2' = map (substWeakTerm (zip xs2 vs1)) ts2
  analyze $ (s1, s2) : zip ts1 ts2' ++ cs

data Stuck
  = StuckPiElim WeakSortal
                Identifier
                [WeakTerm]
  | StuckPiElimStrict WeakSortal
                      Identifier
                      [Identifier]
  | StuckOther

asStuckedTerm :: WeakTerm -> Maybe (Stuck, Identifier)
asStuckedTerm (_ :< WeakTermPiElim s (_ :< WeakTermHole x) es) =
  case mapM interpretAsUpsilon es of
    Nothing -> Just (StuckPiElim s x es, x)
    Just xs -> Just (StuckPiElimStrict s x xs, x)
asStuckedTerm (_ :< WeakTermSigmaElim _ _ e1 _)
  | Just m <- obtainStuckReason e1 = Just (StuckOther, m)
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

interpretAsUpsilon :: WeakTerm -> Maybe Identifier
interpretAsUpsilon (_ :< WeakTermUpsilon x) = Just x
interpretAsUpsilon _                        = Nothing
