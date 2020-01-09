module Elaborate.Analyze
  ( analyze
  , toPiElim
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.List
import Data.Maybe
import qualified Data.PQueue.Min as Q
import System.Timeout
import qualified Text.Show.Pretty as Pr

import Data.Basic
import Data.Constraint
import Data.Env
import Data.WeakTerm
import Reduce.WeakTerm

-- {} analyze {}
analyze :: [PreConstraint] -> WithEnv ConstraintQueue
analyze cs = Q.fromList <$> simp cs

-- {} simp {}
simp :: [PreConstraint] -> WithEnv [EnrichedConstraint]
simp [] = return []
simp ((e1, e2):cs) = do
  me1' <- reduceWeakTermPlus e1 >>= liftIO . timeout 5000000 . return
  me2' <- reduceWeakTermPlus e2 >>= liftIO . timeout 5000000 . return
  case (me1', me2') of
    (Just e1', Just e2') -> simp' $ (e1', e2') : cs
    _ -> throwError $ "cannot simplify [TIMEOUT]:\n" ++ Pr.ppShow (e1, e2)

-- {} simp' {}
simp' :: [PreConstraint] -> WithEnv [EnrichedConstraint]
simp' [] = return []
simp' (((_, e1), (_, e2)):cs)
  | e1 == e2 = simp cs
simp' (((_, WeakTermPi xts1 cod1), (_, WeakTermPi xts2 cod2)):cs)
  | length xts1 == length xts2 = simpBinder xts1 cod1 xts2 cod2 cs
simp' (((_, WeakTermPiIntro xts1 e1), (_, WeakTermPiIntro xts2 e2)):cs)
  | length xts1 == length xts2 = simpBinder xts1 e1 xts2 e2 cs
simp' (((_, WeakTermPiIntro xts body1@(m1, _)), e2@(_, _)):cs) = do
  let vs = map (uncurry toVar) xts
  simp $ (body1, (m1, WeakTermPiElim e2 vs)) : cs
simp' ((e1, e2@(_, WeakTermPiIntro {})):cs) = simp' $ (e2, e1) : cs
simp' (((_, WeakTermMu xt1 e1), (_, WeakTermMu xt2 e2)):cs)
  | fst xt1 == fst xt2 = simpBinder [xt1] e1 [xt2] e2 cs
simp' (((_, WeakTermConstDecl xt1 e1), (_, WeakTermConstDecl xt2 e2)):cs) = do
  simpBinder [xt1] e1 [xt2] e2 cs
simp' (((_, WeakTermInt l1), (_, WeakTermIntS _ l2)):cs)
  | l1 == l2 = simp cs
simp' (((_, WeakTermIntS _ l1), (_, WeakTermInt l2)):cs)
  | l1 == l2 = simp cs
simp' (((_, WeakTermInt l1), (_, WeakTermIntU _ l2)):cs)
  | l1 == l2 = simp cs
simp' (((_, WeakTermIntU _ l1), (_, WeakTermInt l2)):cs)
  | l1 == l2 = simp cs
simp' (((_, WeakTermFloat l1), (_, WeakTermFloat16 l2)):cs)
  | show l1 == show l2 = simp cs
simp' (((_, WeakTermFloat16 l1), (_, WeakTermFloat l2)):cs)
  | show l1 == show l2 = simp cs
simp' (((_, WeakTermFloat l1), (_, WeakTermFloat32 l2)):cs)
  | show l1 == show l2 = simp cs
simp' (((_, WeakTermFloat32 l1), (_, WeakTermFloat l2)):cs)
  | show l1 == show l2 = simp cs
simp' (((_, WeakTermFloat l1), (_, WeakTermFloat64 l2)):cs)
  | l1 == l2 = simp cs
simp' (((_, WeakTermFloat64 l1), (_, WeakTermFloat l2)):cs)
  | l1 == l2 = simp cs
simp' (((_, WeakTermEnumElim e1 les1), (_, WeakTermEnumElim e2 les2)):cs)
  -- using term equality
  | e1 == e2 = do
    csEnum <- simpCase les1 les2
    csCont <- simp cs
    return $ csEnum ++ csCont
simp' (((_, WeakTermArray k1 indexType1), (_, WeakTermArray k2 indexType2)):cs)
  | k1 == k2 = simp $ (indexType1, indexType2) : cs
simp' (((_, WeakTermArrayIntro k1 les1), (_, WeakTermArrayIntro k2 les2)):cs)
  | k1 == k2 = do
    csArray <- simpCase les1 les2
    csCont <- simp cs
    return $ csArray ++ csCont
simp' ((e1, e2):cs)
  | (_, WeakTermPiElim (_, WeakTermConst f) es1) <- e1
  , (_, WeakTermPiElim (_, WeakTermConst g) es2) <- e2
  , f == g
  , length es1 == length es2 = simp $ zip es1 es2 ++ cs
simp' ((e1, e2):cs) = do
  let ms1 = asStuckedTerm e1
  let ms2 = asStuckedTerm e2
  let stuckReasonList = catMaybes [ms1 >>= stuckReasonOf, ms2 >>= stuckReasonOf]
  sub <- gets substEnv
  if any (`elem` map fst sub) stuckReasonList
    then do
      cs' <- simp' cs
      let c = Enriched (e1, e2) stuckReasonList [] $ ConstraintAnalyzable
      return $ c : cs'
    else do
      let hs1 = holeWeakTermPlus e1
      let hs2 = holeWeakTermPlus e2
      case (ms1, ms2) of
        (Just (StuckPiElimStrict h1 ies1), _)
          | xs1 <- concatMap getVarList ies1
          , occurCheck h1 hs2
          , includeCheck xs1 e2
          , linearCheck xs1 -> simpPattern h1 ies1 e1 e2 hs2 cs
        (_, Just (StuckPiElimStrict h2 ies2))
          | xs2 <- concatMap getVarList ies2
          , occurCheck h2 hs1
          , includeCheck xs2 e1
          , linearCheck xs2 -> simpPattern h2 ies2 e2 e1 hs1 cs
        (Just (DeltaPiElim h1 mess1), _)
          | Just (_, body) <- lookup h1 sub ->
            simp $ (toPiElim body mess1, e2) : cs
        (_, Just (DeltaPiElim h2 mess2))
          | Just (_, body) <- lookup h2 sub ->
            simp $ (toPiElim body mess2, e1) : cs
        (Just (StuckPiElimStrict h1 ies1), _)
          | xs1 <- concatMap getVarList ies1
          , occurCheck h1 hs2
          , includeCheck xs1 e2 -> simpQuasiPattern h1 ies1 e1 e2 hs2 cs
        (_, Just (StuckPiElimStrict h2 ies2))
          | xs2 <- concatMap getVarList ies2
          , occurCheck h2 hs1
          , includeCheck xs2 e1 -> simpQuasiPattern h2 ies2 e2 e1 hs1 cs
        (Just (StuckPiElim h1 ies1), Nothing)
          | xs1 <- concatMap getVarList ies1
          , occurCheck h1 hs2
          , includeCheck xs1 e2 -> simpFlexRigid h1 ies1 e1 e2 hs2 cs
        (Nothing, Just (StuckPiElim h2 ies2))
          | xs2 <- concatMap getVarList ies2
          , occurCheck h2 hs1
          , includeCheck xs2 e1 -> simpFlexRigid h2 ies2 e2 e1 hs1 cs
        (Just (StuckPiElimMu (x1, body1, _) mess1), Just (StuckPiElimMu (x2, body2, _) mess2))
          | x1 == x2
          , mess1 == mess2 -> simp $ (body1, body2) : cs
        (Just (StuckPiElimMu (x1, body, self) mess1), _) -> do
          let self' = substWeakTermPlus [(x1, self)] body
          let e1' = toPiElim self' mess1
          simp $ (e1', e2) : cs
        (_, Just (StuckPiElimMu (x2, body, self) mess2)) -> do
          let self' = substWeakTermPlus [(x2, self)] body
          let e2' = toPiElim self' mess2
          simp $ (e1, e2') : cs
        _ -> simpOther e1 e2 (hs1 ++ hs2) cs

simpBinder ::
     [(Identifier, WeakTermPlus)]
  -> WeakTermPlus
  -> [(Identifier, WeakTermPlus)]
  -> WeakTermPlus
  -> [(WeakTermPlus, WeakTermPlus)]
  -> WithEnv [EnrichedConstraint]
simpBinder [] cod1 [] cod2 cs = simp $ (cod1, cod2) : cs
simpBinder ((x1, t1):xts1) cod1 ((x2, t2):xts2) cod2 cs = do
  let var1 = toVar x1 t1
  let (xts2', cod2') = substWeakTermPlusBindingsWithBody [(x2, var1)] xts2 cod2
  cst <- simp [(t1, t2)]
  cs' <- simpBinder xts1 cod1 xts2' cod2' cs
  return $ cst ++ cs'
simpBinder _ _ _ _ _ = throwError "cannot simplify (simpBinder)"

simpCase ::
     (Ord a)
  => [(a, WeakTermPlus)]
  -> [(a, WeakTermPlus)]
  -> WithEnv [EnrichedConstraint]
simpCase les1 les2 = do
  let les1' = sortBy (\x y -> fst x `compare` fst y) les1
  let les2' = sortBy (\x y -> fst x `compare` fst y) les2
  let (ls1, es1) = unzip les1'
  let (ls2, es2) = unzip les2'
  if ls1 /= ls2
    then throwError "cannot simplify (simpCase)"
    else simp $ zip es1 es2

simpPattern ::
     Identifier
  -> [[WeakTermPlus]]
  -> WeakTermPlus
  -> WeakTermPlus
  -> [Identifier]
  -> [(WeakTermPlus, WeakTermPlus)]
  -> WithEnv [EnrichedConstraint]
simpPattern h1 ies1 e1 e2 fmvs cs = do
  cs' <- simp cs
  return $ Enriched (e1, e2) [h1] fmvs (ConstraintPattern h1 ies1 e2) : cs'

simpQuasiPattern ::
     Identifier
  -> [[WeakTermPlus]]
  -> WeakTermPlus
  -> WeakTermPlus
  -> [Identifier]
  -> [(WeakTermPlus, WeakTermPlus)]
  -> WithEnv [EnrichedConstraint]
simpQuasiPattern h1 ies1 e1 e2 fmvs cs = do
  cs' <- simp cs
  return $ Enriched (e1, e2) [h1] fmvs (ConstraintQuasiPattern h1 ies1 e2) : cs'

simpFlexRigid ::
     Hole
  -> [[WeakTermPlus]]
  -> WeakTermPlus
  -> WeakTermPlus
  -> [Identifier]
  -> [PreConstraint]
  -> WithEnv [EnrichedConstraint]
simpFlexRigid h1 ies1 e1 e2 fmvs cs = do
  cs' <- simp cs
  return $ Enriched (e1, e2) [h1] fmvs (ConstraintFlexRigid h1 ies1 e2) : cs'

simpOther ::
     WeakTermPlus
  -> WeakTermPlus
  -> [Hole]
  -> [PreConstraint]
  -> WithEnv [EnrichedConstraint]
simpOther e1 e2 fmvs cs = do
  cs' <- simp cs
  let c = Enriched (e1, e2) fmvs [] $ ConstraintOther
  return $ c : cs'

data Stuck
  = StuckPiElim Hole [[WeakTermPlus]]
  | StuckPiElimStrict Hole [[WeakTermPlus]]
  | StuckPiElimMu
      (Identifier, WeakTermPlus, WeakTermPlus)
      [(PreMeta, [WeakTermPlus])]
  | DeltaPiElim Identifier [(PreMeta, [WeakTermPlus])] -- ここでmetaを保持。

asStuckedTerm :: WeakTermPlus -> Maybe Stuck
asStuckedTerm (_, WeakTermUpsilon x) = Just $ DeltaPiElim x []
asStuckedTerm (_, WeakTermPiElim (_, WeakTermZeta h) es)
  | Just _ <- mapM asUpsilon es = Just $ StuckPiElimStrict h [es]
asStuckedTerm (_, WeakTermPiElim (_, WeakTermZeta h) es) =
  Just $ StuckPiElim h [es]
asStuckedTerm (m, WeakTermPiElim self@(_, WeakTermMu (x, _) body) es) =
  Just $ StuckPiElimMu (x, body, self) [(m, es)]
asStuckedTerm (m, WeakTermPiElim e es)
  | Just _ <- mapM asUpsilon es =
    case asStuckedTerm e of
      Just (StuckPiElim h iess) -> Just $ StuckPiElim h (iess ++ [es])
      Just (StuckPiElimStrict h iexss) ->
        Just $ StuckPiElimStrict h $ iexss ++ [es]
      Just (StuckPiElimMu mu ess) -> Just $ StuckPiElimMu mu $ ess ++ [(m, es)]
      Just (DeltaPiElim x ess) -> Just $ DeltaPiElim x $ ess ++ [(m, es)]
      Nothing -> Nothing
asStuckedTerm (m, WeakTermPiElim e es) =
  case asStuckedTerm e of
    Just (StuckPiElim h iess) -> Just $ StuckPiElim h $ iess ++ [es]
    Just (StuckPiElimStrict h iess) -> do
      Just $ StuckPiElim h $ iess ++ [es]
    Just (StuckPiElimMu mu ess) -> Just $ StuckPiElimMu mu $ ess ++ [(m, es)]
    Just (DeltaPiElim x ess) -> Just $ DeltaPiElim x $ ess ++ [(m, es)]
    Nothing -> Nothing
asStuckedTerm _ = Nothing

stuckReasonOf :: Stuck -> Maybe Hole
stuckReasonOf (StuckPiElim h _) = Just h
stuckReasonOf (StuckPiElimStrict h _) = Just h
stuckReasonOf (StuckPiElimMu {}) = Nothing
stuckReasonOf (DeltaPiElim _ _) = Nothing

occurCheck :: Identifier -> [Identifier] -> Bool
occurCheck h fmvs = h `notElem` fmvs

includeCheck :: [Identifier] -> WeakTermPlus -> Bool
includeCheck xs e = all (`elem` xs) $ varWeakTermPlus e

linearCheck :: [Identifier] -> Bool
linearCheck xs = xs == nub xs

getVarList :: [WeakTermPlus] -> [Identifier]
getVarList xs = catMaybes $ map asUpsilon xs

toVar :: Identifier -> WeakTermPlus -> WeakTermPlus
toVar x t = (PreMetaNonTerminal t emptyMeta, WeakTermUpsilon x)

asUpsilon :: WeakTermPlus -> Maybe Identifier
asUpsilon (_, WeakTermUpsilon x) = Just x
asUpsilon _ = Nothing

toPiElim :: WeakTermPlus -> [(PreMeta, [WeakTermPlus])] -> WeakTermPlus
toPiElim e [] = e
toPiElim e ((m, es):ess) = toPiElim (m, WeakTermPiElim e es) ess
