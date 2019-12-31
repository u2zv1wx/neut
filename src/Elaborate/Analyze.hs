module Elaborate.Analyze
  ( analyze
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
import Data.PreTerm
import Reduce.PreTerm

analyze :: [PreConstraint] -> WithEnv ConstraintQueue
analyze cs = Q.fromList <$> simp cs

simp :: [PreConstraint] -> WithEnv [EnrichedConstraint]
simp [] = return []
simp ((e1, e2):cs)
  | isReduciblePreTerm e1 = simpReduce e1 e2 cs
simp ((e1, e2):cs)
  | isReduciblePreTerm e2 = simpReduce e2 e1 cs
simp cs = simp' cs

simp' :: [PreConstraint] -> WithEnv [EnrichedConstraint]
simp' [] = return []
simp' (((_, PreTermTau), (_, PreTermTau)):cs) = simp cs
simp' (((_, PreTermTheta x), (_, PreTermTheta y)):cs)
  | x == y = simp cs
simp' (((_, PreTermUpsilon x1), (_, PreTermUpsilon x2)):cs)
  | x1 == x2 = simp cs
simp' (((_, PreTermPi xts1 cod1), (_, PreTermPi xts2 cod2)):cs)
  | length xts1 == length xts2 = do simpPi xts1 cod1 xts2 cod2 cs
simp' (((_, PreTermPiIntro xts1 e1), (_, PreTermPiIntro xts2 e2)):cs)
  | length xts1 == length xts2 = do simpPi xts1 e1 xts2 e2 cs
simp' (((_, PreTermPiIntro xts body1@(m1, _)), e2@(_, _)):cs) = do
  let vs = map (uncurry toVar) xts
  simp $ (body1, (m1, PreTermPiElim e2 vs)) : cs
simp' ((e1, e2@(_, PreTermPiIntro {})):cs) = simp' $ (e2, e1) : cs
simp' (((_, PreTermMu (x1, t1) e1), (_, PreTermMu (x2, t2) e2)):cs)
  | x1 == x2 = simp $ (t1, t2) : (e1, e2) : cs
simp' (((_, PreTermZeta x), (_, PreTermZeta y)):cs)
  | x == y = simp cs
simp' (((_, PreTermIntS size1 l1), (_, PreTermIntS size2 l2)):cs)
  | size1 == size2
  , l1 == l2 = simp cs
simp' (((_, PreTermIntU size1 l1), (_, PreTermIntU size2 l2)):cs)
  | size1 == size2
  , l1 == l2 = simp cs
simp' (((_, PreTermInt l1), (_, PreTermIntS _ l2)):cs)
  | l1 == l2 = simp cs
simp' (((_, PreTermIntS _ l1), (_, PreTermInt l2)):cs)
  | l1 == l2 = simp cs
simp' (((_, PreTermInt l1), (_, PreTermIntU _ l2)):cs)
  | l1 == l2 = simp cs
simp' (((_, PreTermIntU _ l1), (_, PreTermInt l2)):cs)
  | l1 == l2 = simp cs
simp' (((_, PreTermInt l1), (_, PreTermInt l2)):cs)
  | l1 == l2 = simp cs
simp' (((_, PreTermFloat16 l1), (_, PreTermFloat16 l2)):cs)
  | l1 == l2 = simp cs
simp' (((_, PreTermFloat32 l1), (_, PreTermFloat32 l2)):cs)
  | l1 == l2 = simp cs
simp' (((_, PreTermFloat64 l1), (_, PreTermFloat64 l2)):cs)
  | l1 == l2 = simp cs
simp' (((_, PreTermFloat l1), (_, PreTermFloat16 l2)):cs)
  | show l1 == show l2 = simp cs
simp' (((_, PreTermFloat16 l1), (_, PreTermFloat l2)):cs)
  | show l1 == show l2 = simp cs
simp' (((_, PreTermFloat l1), (_, PreTermFloat32 l2)):cs)
  | show l1 == show l2 = simp cs
simp' (((_, PreTermFloat32 l1), (_, PreTermFloat l2)):cs)
  | show l1 == show l2 = simp cs
simp' (((_, PreTermFloat l1), (_, PreTermFloat64 l2)):cs)
  | l1 == l2 = simp cs
simp' (((_, PreTermFloat64 l1), (_, PreTermFloat l2)):cs)
  | l1 == l2 = simp cs
simp' (((_, PreTermFloat l1), (_, PreTermFloat l2)):cs)
  | l1 == l2 = simp cs
simp' (((_, PreTermEnum l1), (_, PreTermEnum l2)):cs)
  | l1 == l2 = simp cs
simp' (((_, PreTermEnumIntro l1), (_, PreTermEnumIntro l2)):cs)
  | l1 == l2 = simp cs
simp' (((_, PreTermArray k1 indexType1), (_, PreTermArray k2 indexType2)):cs)
  | k1 == k2 = simp $ (indexType1, indexType2) : cs
simp' (((_, PreTermArrayIntro k1 les1), (_, PreTermArrayIntro k2 les2)):cs)
  | k1 == k2 = do
    csArray <- simpArrayIntro les1 les2
    csCont <- simp cs
    return $ csArray ++ csCont
simp' ((e1, e2):cs)
  | (_, PreTermPiElim (_, PreTermTheta f) es1) <- e1
  , (_, PreTermPiElim (_, PreTermTheta g) es2) <- e2
  , f == g
  , length es1 == length es2 = simp $ zip es1 es2 ++ cs
simp' ((e1, e2):cs) = do
  let ms1 = asStuckedTerm e1
  let ms2 = asStuckedTerm e2
  let hs = catMaybes [ms1 >>= stuckReasonOf, ms2 >>= stuckReasonOf]
  sub <- gets substEnv
  if any (`elem` map fst sub) hs
    then do
      cs' <- simp' cs
      let c = Enriched (e1, e2) hs $ ConstraintAnalyzable
      return $ c : cs'
    else do
      case (ms1, ms2) of
        (Just (StuckPiElimStrict h1 ies1), _)
          | onesided h1 e2
          , xs <- concatMap getVarList ies1
          , subsume e2 xs
          , isDisjoint xs -> simpPattern h1 ies1 e1 e2 cs
        (_, Just (StuckPiElimStrict h2 ies2))
          | onesided h2 e1
          , xs <- concatMap getVarList ies2
          , subsume e1 xs
          , isDisjoint xs -> simpPattern h2 ies2 e2 e1 cs
        (Just (DeltaPiElim h1 mess1), _)
          | Just body <- lookup h1 sub -> simpDelta body mess1 e1 e2 cs
        (_, Just (DeltaPiElim h2 mess2))
          | Just body <- lookup h2 sub -> simpDelta body mess2 e2 e1 cs
        (Just (StuckPiElimStrict h1 ies1), _)
          | onesided h1 e2
          , xs <- concatMap getVarList ies1
          , subsume e2 xs -> simpQuasiPattern h1 ies1 e1 e2 cs
        (_, Just (StuckPiElimStrict h2 ies2))
          | onesided h2 e1
          , xs <- concatMap getVarList ies2
          , subsume e1 xs -> simpQuasiPattern h2 ies2 e2 e1 cs
        (Just (StuckPiElim h1 ies1), Nothing)
          | onesided h1 e2
          , xs <- concatMap getVarList ies1
          , subsume e2 xs -> simpFlexRigid h1 ies1 e1 e2 cs
        (Nothing, Just (StuckPiElim h2 ies2))
          | onesided h2 e1
          , xs <- concatMap getVarList ies2
          , subsume e1 xs -> simpFlexRigid h2 ies2 e2 e1 cs
        _ -> do
          let fmvs = (concatMap holePreTermPlus [e1, e2])
          simpOther e1 e2 fmvs cs

simpReduce ::
     PreTermPlus
  -> PreTermPlus
  -> [PreConstraint]
  -> WithEnv [EnrichedConstraint]
simpReduce e1 e2 cs = do
  me1' <- reducePreTermPlus e1 >>= liftIO . timeout 5000000 . return
  case me1' of
    Just e1'
      | isReduciblePreTerm e2 -> simpReduce' e2 e1' cs
    Just e1' -> simp' $ (e1', e2) : cs
    Nothing -> throwError $ "cannot simplify [TIMEOUT]:\n" ++ Pr.ppShow (e1, e2)

simpReduce' ::
     PreTermPlus
  -> PreTermPlus
  -> [PreConstraint]
  -> WithEnv [EnrichedConstraint]
simpReduce' e1 e2 cs = do
  me1' <- reducePreTermPlus e1 >>= liftIO . timeout 5000000 . return
  case me1' of
    Just e1' -> simp' $ (e1', e2) : cs
    Nothing -> throwError $ "cannot simplify [TIMEOUT]:\n" ++ Pr.ppShow (e1, e2)

simpPi ::
     [(Identifier, PreTermPlus)]
  -> PreTermPlus
  -> [(Identifier, PreTermPlus)]
  -> PreTermPlus
  -> [(PreTermPlus, PreTermPlus)]
  -> WithEnv [EnrichedConstraint]
simpPi [] cod1 [] cod2 cs = simp $ (cod1, cod2) : cs
simpPi ((x1, t1):xts1) cod1 ((x2, t2):xts2) cod2 cs = do
  let var1 = toVar x1 t1
  let (xts2', cod2') = substPreTermPlusBindingsWithBody [(x2, var1)] xts2 cod2
  cst <- simp [(t1, t2)]
  cs' <- simpPi xts1 cod1 xts2' cod2' cs
  return $ cst ++ cs'
simpPi _ _ _ _ _ = throwError "cannot simplify (Pi)"

simpArrayIntro ::
     [(EnumValue, PreTermPlus)]
  -> [(EnumValue, PreTermPlus)]
  -> WithEnv [EnrichedConstraint]
simpArrayIntro les1 les2 = do
  let les1' = sortBy (\x y -> fst x `compare` fst y) les1
  let les2' = sortBy (\x y -> fst x `compare` fst y) les2
  let (ls1, es1) = unzip les1'
  let (ls2, es2) = unzip les2'
  if ls1 /= ls2
    then throwError "simpArrayIntro"
    else simp $ zip es1 es2

simpPattern ::
     Identifier
  -> [[PreTermPlus]]
  -> PreTermPlus
  -> PreTermPlus
  -> [(PreTermPlus, PreTermPlus)]
  -> WithEnv [EnrichedConstraint]
simpPattern h1 ies1 e1 e2 cs = do
  cs' <- simp cs
  return $ Enriched (e1, e2) [h1] (ConstraintPattern h1 ies1 e2) : cs'

simpDelta ::
     PreTermPlus
  -> [(PreMeta, [PreTermPlus])]
  -> PreTermPlus
  -> PreTermPlus
  -> [(PreTermPlus, PreTermPlus)]
  -> WithEnv [EnrichedConstraint]
simpDelta body mes1 e1 e2 cs = do
  cs' <- simp cs
  return $ Enriched (e1, e2) [] (ConstraintDelta body mes1 e2) : cs'

simpQuasiPattern ::
     Identifier
  -> [[PreTermPlus]]
  -> PreTermPlus
  -> PreTermPlus
  -> [(PreTermPlus, PreTermPlus)]
  -> WithEnv [EnrichedConstraint]
simpQuasiPattern h1 ies1 e1 e2 cs = do
  cs' <- simp cs
  let fmvs = (concatMap holePreTermPlus [e1, e2])
  return $ Enriched (e1, e2) fmvs (ConstraintQuasiPattern h1 ies1 e2) : cs'

simpFlexRigid ::
     Hole
  -> [[PreTermPlus]]
  -> PreTermPlus
  -> PreTermPlus
  -> [PreConstraint]
  -> WithEnv [EnrichedConstraint]
simpFlexRigid h1 ies1 e1 e2 cs = do
  cs' <- simp cs
  let fmvs = (concatMap holePreTermPlus [e1, e2])
  return $ Enriched (e1, e2) fmvs (ConstraintFlexRigid h1 ies1 e2) : cs'

simpOther ::
     PreTermPlus
  -> PreTermPlus
  -> [Hole]
  -> [PreConstraint]
  -> WithEnv [EnrichedConstraint]
simpOther e1 e2 fmvs cs = do
  cs' <- simp cs
  let c = Enriched (e1, e2) fmvs $ ConstraintOther
  return $ c : cs'

data Stuck
  = StuckPiElim Hole [[PreTermPlus]]
  | StuckPiElimStrict Hole [[PreTermPlus]]
  | DeltaPiElim Identifier [(PreMeta, [PreTermPlus])] -- ここでmetaを保持。

asStuckedTerm :: PreTermPlus -> Maybe Stuck
asStuckedTerm (_, PreTermPiElim (_, PreTermZeta h) es)
  | Just _ <- mapM asUpsilon es = Just $ StuckPiElimStrict h [es]
asStuckedTerm (_, PreTermPiElim (_, PreTermZeta h) es) =
  Just $ StuckPiElim h [es]
asStuckedTerm (m, PreTermPiElim (_, PreTermUpsilon x) es) =
  Just $ DeltaPiElim x [(m, es)]
asStuckedTerm (m, PreTermPiElim e es)
  | Just _ <- mapM asUpsilon es =
    case asStuckedTerm e of
      Just (StuckPiElim h iess) -> Just $ StuckPiElim h (iess ++ [es])
      Just (StuckPiElimStrict h iexss) ->
        Just $ StuckPiElimStrict h $ iexss ++ [es]
      Just (DeltaPiElim x ess) -> Just $ DeltaPiElim x $ ess ++ [(m, es)]
      Nothing -> Nothing
asStuckedTerm (m, PreTermPiElim e es) =
  case asStuckedTerm e of
    Just (StuckPiElim h iess) -> Just $ StuckPiElim h $ iess ++ [es]
    Just (StuckPiElimStrict h iess) -> do
      Just $ StuckPiElim h $ iess ++ [es]
    Just (DeltaPiElim x ess) -> Just $ DeltaPiElim x $ ess ++ [(m, es)]
    Nothing -> Nothing
asStuckedTerm _ = Nothing

stuckReasonOf :: Stuck -> Maybe Hole
stuckReasonOf (StuckPiElim h _) = Just h
stuckReasonOf (StuckPiElimStrict h _) = Just h
stuckReasonOf (DeltaPiElim _ _) = Nothing

onesided :: Identifier -> PreTermPlus -> Bool
onesided h e = h `notElem` holePreTermPlus e

subsume :: PreTermPlus -> [Identifier] -> Bool
subsume e xs = all (`elem` xs) $ varPreTermPlus e

isDisjoint :: [Identifier] -> Bool
isDisjoint xs = xs == nub xs

getVarList :: [PreTermPlus] -> [Identifier]
getVarList xs = catMaybes $ map asUpsilon xs

toVar :: Identifier -> PreTermPlus -> PreTermPlus
toVar x t = (PreMetaNonTerminal t Nothing, PreTermUpsilon x)

asUpsilon :: PreTermPlus -> Maybe Identifier
asUpsilon (_, PreTermUpsilon x) = Just x
asUpsilon _ = Nothing
