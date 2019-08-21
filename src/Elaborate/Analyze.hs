module Elaborate.Analyze
  ( analyze
  , simp
  ) where

import           Control.Monad.Except
import           Control.Monad.State
import           Data.IORef
import qualified Data.PQueue.Min      as Q
import           System.Timeout
import qualified Text.Show.Pretty     as Pr

import           Data.Basic
import           Data.Constraint
import           Data.Env
import           Data.WeakTerm
import           Elaborate.Infer      (readWeakMetaType, writeWeakMetaType)
import           Reduce.WeakTerm

analyze :: [PreConstraint] -> WithEnv ()
analyze cs = do
  cs' <- Q.fromList <$> simp cs
  modify (\e -> e {constraintQueue = cs' `Q.union` constraintQueue e})

simp :: [PreConstraint] -> WithEnv [EnrichedConstraint]
simp [] = return []
simp ((e1, e2):cs)
  | isReducible e1 = do
    me1' <-
      reduceWeakTermPlus e1 >>= \e1' -> liftIO $ timeout 5000000 $ return e1'
    case me1' of
      Just e1' -> simp $ (e1', e2) : cs
      Nothing ->
        throwError $ "cannot simplify [TIMEOUT]:\n" ++ Pr.ppShow (e1, e2)
simp ((e1, e2):cs)
  | isReducible e2 = simp $ (e2, e1) : cs
simp (((m1, WeakTermTau), (m2, WeakTermTau)):cs) = simpMetaRet m1 m2 (simp cs)
simp (((m1, WeakTermTheta x), (m2, WeakTermTheta y)):cs)
  | x == y = simpMetaRet m1 m2 (simp cs)
simp (((m1, WeakTermUpsilon x1), (m2, WeakTermUpsilon x2)):cs)
  | x1 == x2 = simpMetaRet m1 m2 (simp cs)
simp (((m1, WeakTermEpsilon l1), (m2, WeakTermEpsilon l2)):cs)
  | l1 == l2 = simpMetaRet m1 m2 (simp cs)
simp (((m1, WeakTermEpsilonIntro l1), (m2, WeakTermEpsilonIntro l2)):cs)
  | l1 == l2 = simpMetaRet m1 m2 (simp cs)
simp (((m1, WeakTermPi xts1 t1), (m2, WeakTermPi xts2 t2)):cs)
  | length xts1 == length xts2 =
    simpMetaRet m1 m2 $ simpBinder xts1 t1 xts2 t2 cs
simp (((m1, WeakTermPiIntro xts1 e1), (m2, WeakTermPiIntro xts2 e2)):cs) =
  simpMetaRet m1 m2 $ simpBinder xts1 e1 xts2 e2 cs
  -- h1 <- newNameWith "hole"
  -- h2 <- newNameWith "hole"
  -- simpMetaRet m1 m2 $ simpPiOrSigma (xts1 ++ [(h1, e1)]) (xts2 ++ [(h2, e2)]) cs
simp (((m1, WeakTermPiIntro xts body1@(bodyMeta, _)), e2@(m2, _)):cs) = do
  vs <- mapM (uncurry toVar) xts
  mt <- readWeakMetaType bodyMeta
  appMeta <- newMeta
  writeWeakMetaType appMeta mt
  let comp = simp $ (body1, (appMeta, WeakTermPiElim e2 vs)) : cs
  simpMetaRet m1 m2 comp
simp ((e1, e2@(_, WeakTermPiIntro {})):cs) = simp $ (e2, e1) : cs
simp (((m1, WeakTermSigma xts1 t1), (m2, WeakTermSigma xts2 t2)):cs)
  | length xts1 == length xts2 =
    simpMetaRet m1 m2 $ simpBinder xts1 t1 xts2 t2 cs
simp (((m1, WeakTermSigmaIntro es1), (m2, WeakTermSigmaIntro es2)):cs)
  | length es1 == length es2 = simpMetaRet m1 m2 $ simp $ zip es1 es2 ++ cs
simp ((e1, e2):cs)
  | (m1, WeakTermPiElim (_, WeakTermUpsilon f) es1) <- e1
  , (m2, WeakTermPiElim (_, WeakTermUpsilon g) es2) <- e2
  , f == g
  , length es1 == length es2 = simpMetaRet m1 m2 $ simp $ zip es1 es2 ++ cs
simp ((e1@(m1, _), e2@(m2, _)):cs) = do
  let ms1 = asStuckedTerm e1
  let ms2 = asStuckedTerm e2
  case (ms1, ms2) of
    (Just (StuckHole h), _) -> do
      cs' <- simpMetaRet m1 m2 $ simp cs
      return $ Enriched (e1, e2) [h] (ConstraintImmediate h e2) : cs'
    (_, Just (StuckHole _)) -> simp $ (e2, e1) : cs
    (Just (StuckPiElimStrict h1 exs1), _)
      | all (isSolvable e2 h1) (map (map snd) exs1) -> do
        cs' <- simpMetaRet m1 m2 $ simp cs
        let es1 = map (map fst) exs1
        return $ Enriched (e1, e2) [h1] (ConstraintPattern h1 es1 e2) : cs'
    (_, Just (StuckPiElimStrict h2 exs2))
      | all (isSolvable e1 h2) (map (map snd) exs2) ->
        simpMetaRet m1 m2 $ simp $ (e2, e1) : cs
    (Just (StuckPiElimStrict h1 exs1), _) -> do
      cs' <- simpMetaRet m1 m2 $ simp cs
      let es1 = map (map fst) exs1
      return $ Enriched (e1, e2) [h1] (ConstraintQuasiPattern h1 es1 e2) : cs'
    (_, Just StuckPiElimStrict {}) -> simp $ (e2, e1) : cs
    (Just (StuckPiElim h1 ies1), Nothing) -> do
      cs' <- simpMetaRet m1 m2 $ simp cs
      let c = Enriched (e1, e2) [h1] $ ConstraintFlexRigid h1 ies1 e2
      return $ c : cs'
    (Nothing, Just StuckPiElim {}) -> simp $ (e2, e1) : cs
    (Just (StuckPiElim h1 ies1), _) -> do
      cs' <- simpMetaRet m1 m2 $ simp cs
      let c = Enriched (e1, e2) [h1] $ ConstraintFlexFlex h1 ies1 e2
      return $ c : cs'
    (_, Just StuckPiElim {}) -> simp $ (e2, e1) : cs
    (Just (StuckOther h1), _) -> do
      cs' <- simpMetaRet m1 m2 $ simp cs
      let c = Enriched (e1, e2) [h1] ConstraintOther
      return $ c : cs'
    (_, Just (StuckOther _)) -> simp $ (e2, e1) : cs
    _ -> throwError $ "cannot simplify:\n" ++ Pr.ppShow (e1, e2)

simpMetaRet ::
     WeakMeta
  -> WeakMeta
  -> WithEnv [EnrichedConstraint]
  -> WithEnv [EnrichedConstraint]
simpMetaRet m1 m2 comp = do
  cs1 <- simpMeta m1 m2
  cs2 <- comp
  return $ cs1 ++ cs2

simpMeta :: WeakMeta -> WeakMeta -> WithEnv [EnrichedConstraint]
simpMeta (WeakMetaTerminal _) (WeakMetaTerminal _) = return []
simpMeta (WeakMetaTerminal _) m2@(WeakMetaNonTerminal _ _) = do
  r1 <- liftIO $ newIORef (Just (newMetaTerminal, WeakTermTau))
  simpMeta (WeakMetaNonTerminal (Ref r1) Nothing) m2
simpMeta m1@WeakMetaNonTerminal {} m2@(WeakMetaTerminal _) = simpMeta m2 m1
simpMeta (WeakMetaNonTerminal (Ref r1) _) (WeakMetaNonTerminal (Ref r2) _) = do
  mt1 <- liftIO $ readIORef r1
  mt2 <- liftIO $ readIORef r2
  case (mt1, mt2) of
    (Just t1, Just t2) -> simp [(t1, t2)]
    (Just _, Nothing)  -> liftIO (writeIORef r2 mt1) >> return []
    (Nothing, Just _)  -> liftIO (writeIORef r1 mt2) >> return []
    _                  -> return []

simpBinder ::
     [IdentifierPlus]
  -> WeakTermPlus
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> [PreConstraint]
  -> WithEnv [EnrichedConstraint]
simpBinder xts1 t1 xts2 t2 cs = do
  vs1' <- mapM (uncurry toVar) xts1
  let s = substWeakTermPlus (zip (map fst xts2) vs1')
  simp $ zip (map snd xts1) (map (s . snd) xts2) ++ [(t1, s t2)] ++ cs

data Stuck
  = StuckHole Hole
  | StuckPiElim Hole
                [[WeakTermPlus]]
  | StuckPiElimStrict Hole
                      [[(WeakTermPlus, Identifier)]]
  | StuckOther Hole

asStuckedTerm :: WeakTermPlus -> Maybe Stuck
asStuckedTerm (_, WeakTermPiElim e es)
  | Just xs <- mapM interpretAsUpsilon es =
    case asStuckedTerm e of
      Just (StuckHole h) -> Just $ StuckPiElimStrict h [zip es xs]
      Just (StuckPiElim h iess) -> Just $ StuckPiElim h (iess ++ [es])
      Just (StuckPiElimStrict h iexss) ->
        Just $ StuckPiElimStrict h $ iexss ++ [zip es xs]
      Just (StuckOther h) -> Just $ StuckOther h
      Nothing -> Nothing
asStuckedTerm (_, WeakTermPiElim e es) =
  case asStuckedTerm e of
    Just (StuckHole h) -> Just $ StuckPiElim h [es]
    Just (StuckPiElim h iess) -> Just $ StuckPiElim h $ iess ++ [es]
    Just (StuckPiElimStrict h exss) -> do
      let ess = map (map fst) exss
      Just $ StuckPiElim h $ ess ++ [es]
    Just (StuckOther h) -> Just $ StuckOther h
    Nothing -> Nothing
asStuckedTerm (_, WeakTermZeta h) = Just $ StuckHole h
asStuckedTerm e
  | Just h <- obtainStuckReason e = Just $ StuckOther h
asStuckedTerm _ = Nothing

obtainStuckReason :: WeakTermPlus -> Maybe Hole
obtainStuckReason (_, WeakTermEpsilonElim _ e _) = obtainStuckReason e
obtainStuckReason (_, WeakTermPiElim e _)        = obtainStuckReason e
obtainStuckReason (_, WeakTermSigmaElim _ e1 _)  = obtainStuckReason e1
obtainStuckReason (_, WeakTermZeta x)            = Just x
obtainStuckReason _                              = Nothing

isSolvable :: WeakTermPlus -> Identifier -> [Identifier] -> Bool
isSolvable e x xs = do
  let (fvs, fmvs) = varWeakTermPlus e
  affineCheck xs fvs && x `notElem` fmvs

toVar :: Identifier -> WeakTermPlus -> WithEnv WeakTermPlus
toVar x t = do
  meta <- newMetaOfType t
  return (meta, WeakTermUpsilon x)

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

interpretAsUpsilon :: WeakTermPlus -> Maybe Identifier
interpretAsUpsilon (_, WeakTermUpsilon x) = Just x
interpretAsUpsilon _                      = Nothing
