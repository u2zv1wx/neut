module Elaborate.Analyze
  ( analyze
  , simp
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.List
import qualified Data.PQueue.Min as Q
import System.Timeout
import qualified Text.Show.Pretty as Pr

import Data.Basic
import Data.Constraint
import Data.Env
import Data.WeakTerm
import Elaborate.Infer (obtainType, univ)
import Reduce.WeakTerm

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
simp (((m1, WeakTermPi xts1 cod1), (m2, WeakTermPi xts2 cod2)):cs)
  | length xts1 == length xts2 =
    simpMetaRet m1 m2 $ simpBinder xts1 cod1 xts2 cod2 cs
simp (((m1, WeakTermPiIntro xts1 e1), (m2, WeakTermPiIntro xts2 e2)):cs)
  | length xts1 == length xts2 =
    simpMetaRet m1 m2 $ simpBinder xts1 e1 xts2 e2 cs
simp (((m1, WeakTermPiIntro xts body1@(bodyMeta, _)), e2@(m2, _)):cs) = do
  vs <- mapM (uncurry toVar) xts
  t <- obtainType bodyMeta
  appMeta <- newMetaOfType t
  let comp = simp $ (body1, (appMeta, WeakTermPiElim e2 vs)) : cs
  simpMetaRet m1 m2 comp
simp ((e1, e2@(_, WeakTermPiIntro {})):cs) = simp $ (e2, e1) : cs
simp ((e1, e2):cs)
  | (m11, WeakTermPiElim (m12, WeakTermUpsilon f) es1) <- e1
  , (m21, WeakTermPiElim (m22, WeakTermUpsilon g) es2) <- e2
  , f == g
  , length es1 == length es2 =
    simpMetaRet' [(m11, m21), (m12, m22)] $ simp $ zip es1 es2 ++ cs
simp ((e1, e2):cs)
  | (m11, WeakTermPiElim (m12, WeakTermTheta f) es1) <- e1
  , (m21, WeakTermPiElim (m22, WeakTermTheta g) es2) <- e2
  , f == g
  , length es1 == length es2 =
    simpMetaRet' [(m11, m21), (m12, m22)] $ simp $ zip es1 es2 ++ cs
simp (((m1, WeakTermIntS size1 l1), (m2, WeakTermIntS size2 l2)):cs)
  | size1 == size2
  , l1 == l2 = simpMetaRet m1 m2 (simp cs)
simp (((m1, WeakTermIntU size1 l1), (m2, WeakTermIntU size2 l2)):cs)
  | size1 == size2
  , l1 == l2 = simpMetaRet m1 m2 (simp cs)
simp (((m1, WeakTermInt l1), (m2, WeakTermIntS _ l2)):cs)
  | l1 == l2 = simpMetaRet m1 m2 (simp cs)
simp (((m1, WeakTermIntS _ l1), (m2, WeakTermInt l2)):cs)
  | l1 == l2 = simpMetaRet m1 m2 (simp cs)
simp (((m1, WeakTermInt l1), (m2, WeakTermIntU _ l2)):cs)
  | l1 == l2 = simpMetaRet m1 m2 (simp cs)
simp (((m1, WeakTermIntU _ l1), (m2, WeakTermInt l2)):cs)
  | l1 == l2 = simpMetaRet m1 m2 (simp cs)
simp (((m1, WeakTermInt l1), (m2, WeakTermInt l2)):cs)
  | l1 == l2 = simpMetaRet m1 m2 (simp cs)
simp (((m1, WeakTermFloat16 l1), (m2, WeakTermFloat16 l2)):cs)
  | l1 == l2 = simpMetaRet m1 m2 (simp cs)
simp (((m1, WeakTermFloat32 l1), (m2, WeakTermFloat32 l2)):cs)
  | l1 == l2 = simpMetaRet m1 m2 (simp cs)
simp (((m1, WeakTermFloat64 l1), (m2, WeakTermFloat64 l2)):cs)
  | l1 == l2 = simpMetaRet m1 m2 (simp cs)
simp (((m1, WeakTermFloat l1), (m2, WeakTermFloat16 l2)):cs)
  | show l1 == show l2 = simpMetaRet m1 m2 (simp cs)
simp (((m1, WeakTermFloat16 l1), (m2, WeakTermFloat l2)):cs)
  | show l1 == show l2 = simpMetaRet m1 m2 (simp cs)
simp (((m1, WeakTermFloat l1), (m2, WeakTermFloat32 l2)):cs)
  | show l1 == show l2 = simpMetaRet m1 m2 (simp cs)
simp (((m1, WeakTermFloat32 l1), (m2, WeakTermFloat l2)):cs)
  | show l1 == show l2 = simpMetaRet m1 m2 (simp cs)
simp (((m1, WeakTermFloat l1), (m2, WeakTermFloat64 l2)):cs)
  | l1 == l2 = simpMetaRet m1 m2 (simp cs)
simp (((m1, WeakTermFloat64 l1), (m2, WeakTermFloat l2)):cs)
  | l1 == l2 = simpMetaRet m1 m2 (simp cs)
simp (((m1, WeakTermFloat l1), (m2, WeakTermFloat l2)):cs)
  | l1 == l2 = simpMetaRet m1 m2 (simp cs)
simp (((m1, WeakTermEnum l1), (m2, WeakTermEnum l2)):cs)
  | l1 == l2 = simpMetaRet m1 m2 (simp cs)
simp (((m1, WeakTermEnumIntro l1), (m2, WeakTermEnumIntro l2)):cs)
  | l1 == l2 = simpMetaRet m1 m2 (simp cs)
simp (((m1, WeakTermArray k1 dom1 cod1), (m2, WeakTermArray k2 dom2 cod2)):cs)
  | k1 == k2 = simpMetaRet m1 m2 $ simp $ (dom1, dom2) : (cod1, cod2) : cs
simp (((m1, WeakTermArrayIntro k1 les1), (m2, WeakTermArrayIntro k2 les2)):cs)
  | k1 == k2 = do
    csArray <- simpArrayIntro les1 les2
    csCont <- simpMetaRet m1 m2 $ simp cs
    return $ csArray ++ csCont
simp ((e1, e2):cs)
  | (m1, WeakTermArrayElim k1 (_, WeakTermUpsilon f) eps1) <- e1
  , (m2, WeakTermArrayElim k2 (_, WeakTermUpsilon g) eps2) <- e2
  , k1 == k2
  , f == g = simpMetaRet m1 m2 $ simp $ (eps1, eps2) : cs
simp ((e1, e2):cs) = do
  let ms1 = asStuckedTerm e1
  let ms2 = asStuckedTerm e2
  case (ms1, ms2) of
    (Just (StuckHole h), _) -> do
      cs' <- simpMetaRet (fst e1) (fst e2) $ simp cs
      fmvs <- takeMetaVarList e1 e2
      return $ Enriched (e1, e2) fmvs (ConstraintImmediate h e2) : cs'
    (_, Just (StuckHole _)) -> simp $ (e2, e1) : cs
    (Just (StuckPiElimStrict h1 exs1), _) ->
      simpPatIfPossible ms1 ms2 h1 exs1 $ (e1, e2) : cs
    (_, Just (StuckPiElimStrict h2 exs2)) ->
      simpPatIfPossible ms2 ms1 h2 exs2 $ (e2, e1) : cs
    _ -> simpStuck ms1 ms2 $ (e1, e2) : cs

takeMetaVarList :: WeakTermPlus -> WeakTermPlus -> WithEnv [Identifier]
takeMetaVarList e1 e2 = do
  (_, fmvs1) <- varWeakTermPlus e1
  (_, fmvs2) <- varWeakTermPlus e2
  return $ fmvs1 ++ fmvs2

simpPatIfPossible ::
     Maybe Stuck
  -> Maybe Stuck
  -> Identifier
  -> [[(WeakTermPlus, Identifier)]]
  -> [((WeakMeta, WeakTerm), WeakTermPlus)]
  -> WithEnv [EnrichedConstraint]
simpPatIfPossible _ _ _ _ [] = return []
simpPatIfPossible ms1 ms2 h1 exs1 ((e1, e2):cs) = do
  isPattern <- allM (isSolvable e2 h1) (map (map snd) exs1)
  if isPattern
    then do
      cs' <- simpMetaRet (fst e1) (fst e2) $ simp cs
      let es1 = map (map fst) exs1
      fmvs <- takeMetaVarList e1 e2
      return $ Enriched (e1, e2) fmvs (ConstraintPattern h1 es1 e2) : cs'
    else simpStuck ms1 ms2 $ (e1, e2) : cs

simpStuck ::
     Maybe Stuck
  -> Maybe Stuck
  -> [((WeakMeta, WeakTerm), (WeakMeta, WeakTerm))]
  -> WithEnv [EnrichedConstraint]
simpStuck _ _ [] = return []
simpStuck ms1 ms2 ((e1, e2):cs) =
  case (ms1, ms2) of
    (Just (StuckPiElimStrict h1 exs1), _) -> do
      cs' <- simpMetaRet (fst e1) (fst e2) $ simp cs
      let es1 = map (map fst) exs1
      fmvs <- takeMetaVarList e1 e2
      return $ Enriched (e1, e2) fmvs (ConstraintQuasiPattern h1 es1 e2) : cs'
    (_, Just StuckPiElimStrict {}) -> simpStuck ms2 ms1 $ (e2, e1) : cs
    (Just (StuckPiElim h1 ies1), Nothing) -> do
      cs' <- simpMetaRet (fst e1) (fst e2) $ simp cs
      fmvs <- takeMetaVarList e1 e2
      let c = Enriched (e1, e2) fmvs $ ConstraintFlexRigid h1 ies1 e2
      return $ c : cs'
    (Nothing, Just StuckPiElim {}) -> simpStuck ms2 ms1 $ (e2, e1) : cs
    (Just (StuckPiElim h1 ies1), Just (StuckPiElim _ _)) -> do
      cs' <- simpMetaRet (fst e1) (fst e2) $ simp cs
      fmvs <- takeMetaVarList e1 e2
      let c = Enriched (e1, e2) fmvs $ ConstraintFlexFlex h1 ies1 e2
      return $ c : cs'
    _ -> throwError $ "cannot simplify:\n" ++ Pr.ppShow (e1, e2) -- ここでcsについても処理をおこなうと複数のエラーを検出できる

simpMetaRet ::
     WeakMeta
  -> WeakMeta
  -> WithEnv [EnrichedConstraint]
  -> WithEnv [EnrichedConstraint]
simpMetaRet m1 m2 comp = do
  cs1 <- simpMeta m1 m2
  cs2 <- comp
  return $ cs1 ++ cs2

simpMetaRet' ::
     [(WeakMeta, WeakMeta)]
  -> WithEnv [EnrichedConstraint]
  -> WithEnv [EnrichedConstraint]
simpMetaRet' mms comp = do
  cs1 <- mapM (\(m1, m2) -> simpMeta m1 m2) mms
  cs2 <- comp
  return $ concat cs1 ++ cs2

simpMeta :: WeakMeta -> WeakMeta -> WithEnv [EnrichedConstraint]
simpMeta (WeakMetaTerminal _) (WeakMetaTerminal _) = return []
simpMeta (WeakMetaTerminal _) m2@(WeakMetaNonTerminal _ _) = do
  r <- newWeakTermRef $ Just univ
  simpMeta (WeakMetaNonTerminal r Nothing) m2
simpMeta m1@WeakMetaNonTerminal {} m2@(WeakMetaTerminal _) = simpMeta m2 m1
simpMeta (WeakMetaNonTerminal ref1 _) (WeakMetaNonTerminal ref2 _) = do
  t1 <- readWeakTermRef ref1
  t2 <- readWeakTermRef ref2
  simp [(t1, t2)]

simpBinder ::
     [IdentifierPlus]
  -> WeakTermPlus
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> [PreConstraint]
  -> WithEnv [EnrichedConstraint]
simpBinder xts1 t1 xts2 t2 cs = do
  h1 <- newNameWith "hole"
  h2 <- newNameWith "hole"
  simpBinder' (xts1 ++ [(h1, t1)]) (xts2 ++ [(h2, t2)]) cs

simpBinder' ::
     [IdentifierPlus]
  -> [IdentifierPlus]
  -> [PreConstraint]
  -> WithEnv [EnrichedConstraint]
simpBinder' xts1 xts2 cs = do
  vs1' <- mapM (uncurry toVar) xts1
  let s = substWeakTermPlus (zip (map fst xts2) vs1')
  xts2' <- mapM (s . snd) xts2
  simp $ zip (map snd xts1) xts2' ++ cs

simpArrayIntro ::
     [(EnumValue, WeakTermPlus)]
  -> [(EnumValue, WeakTermPlus)]
  -> WithEnv [EnrichedConstraint]
simpArrayIntro les1 les2 = do
  let les1' = sortBy (\x y -> fst x `compare` fst y) les1
  let les2' = sortBy (\x y -> fst x `compare` fst y) les2
  let (ls1, es1) = unzip les1'
  let (ls2, es2) = unzip les2'
  if ls1 /= ls2
    then throwError "simpArrayIntro"
    else simp $ zip es1 es2

data Stuck
  = StuckHole Hole
  | StuckPiElim Hole [[WeakTermPlus]]
  | StuckPiElimStrict Hole [[(WeakTermPlus, Identifier)]]

-- a stucked term is a term that cannot be evaluated due to unresolved holes.
asStuckedTerm :: WeakTermPlus -> Maybe Stuck
asStuckedTerm (_, WeakTermPiElim e es)
  | Just xs <- mapM interpretAsUpsilon es =
    case asStuckedTerm e of
      Just (StuckHole h) -> Just $ StuckPiElimStrict h [zip es xs]
      Just (StuckPiElim h iess) -> Just $ StuckPiElim h (iess ++ [es])
      Just (StuckPiElimStrict h iexss) ->
        Just $ StuckPiElimStrict h $ iexss ++ [zip es xs]
      Nothing -> Nothing
asStuckedTerm (_, WeakTermPiElim e es) =
  case asStuckedTerm e of
    Just (StuckHole h) -> Just $ StuckPiElim h [es]
    Just (StuckPiElim h iess) -> Just $ StuckPiElim h $ iess ++ [es]
    Just (StuckPiElimStrict h exss) -> do
      let ess = map (map fst) exss
      Just $ StuckPiElim h $ ess ++ [es]
    Nothing -> Nothing
asStuckedTerm (_, WeakTermZeta h) = Just $ StuckHole h
asStuckedTerm _ = Nothing

isSolvable :: WeakTermPlus -> Identifier -> [Identifier] -> WithEnv Bool
isSolvable e x xs = do
  (fvs, fmvs) <- varWeakTermPlus e
  return $ affineCheck xs fvs && x `notElem` fmvs

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
interpretAsUpsilon _ = Nothing

allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM _ [] = return True
allM p (x:xs) = do
  b1 <- p x
  b2 <- allM p xs
  return $ b1 && b2
