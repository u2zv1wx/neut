module Elaborate.Analyze
  ( analyze
  ) where

import Control.Monad.Except
import Data.List
import Data.Maybe
import qualified Data.PQueue.Min as Q
import System.Timeout
import qualified Text.Show.Pretty as Pr

import Data.Basic
import Data.Constraint
import Data.Env
import Data.PreTerm
import Elaborate.Infer (metaTerminal, typeOf, univ)
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
simp' (((m1, PreTermTau), (m2, PreTermTau)):cs) =
  simpMetaRet [(m1, m2)] (simp cs)
simp' (((m1, PreTermTheta x), (m2, PreTermTheta y)):cs)
  | x == y = simpMetaRet [(m1, m2)] (simp cs)
simp' (((m1, PreTermUpsilon x1), (m2, PreTermUpsilon x2)):cs)
  | x1 == x2 = simpMetaRet [(m1, m2)] (simp cs)
simp' (((m1, PreTermPi xts1 cod1), (m2, PreTermPi xts2 cod2)):cs) = do
  simpPi m1 xts1 cod1 m2 xts2 cod2 cs
simp' (((m1, PreTermPiIntro xts1 e1), (m2, PreTermPiIntro xts2 e2)):cs) =
  simpPi m1 xts1 e1 m2 xts2 e2 cs
simp' (((m1, PreTermPiIntro xts body1), e2@(m2, _)):cs) = do
  vs <- mapM (uncurry toVar) xts
  let appMeta = (PreMetaNonTerminal (typeOf body1) Nothing)
  simpMetaRet [(m1, m2)] $ simp $ (body1, (appMeta, PreTermPiElim e2 vs)) : cs
simp' ((e1, e2@(_, PreTermPiIntro {})):cs) = simp $ (e2, e1) : cs
simp' (((m1, PreTermMu (x1, t1) e1), (m2, PreTermMu (x2, t2) e2)):cs)
  | x1 == x2 = simpMetaRet [(m1, m2)] $ simp $ (t1, t2) : (e1, e2) : cs
simp' (((m1, PreTermZeta x), (m2, PreTermZeta y)):cs)
  | x == y = simpMetaRet [(m1, m2)] (simp cs)
simp' (((m1, PreTermIntS size1 l1), (m2, PreTermIntS size2 l2)):cs)
  | size1 == size2
  , l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp' (((m1, PreTermIntU size1 l1), (m2, PreTermIntU size2 l2)):cs)
  | size1 == size2
  , l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp' (((m1, PreTermInt l1), (m2, PreTermIntS _ l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp' (((m1, PreTermIntS _ l1), (m2, PreTermInt l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp' (((m1, PreTermInt l1), (m2, PreTermIntU _ l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp' (((m1, PreTermIntU _ l1), (m2, PreTermInt l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp' (((m1, PreTermInt l1), (m2, PreTermInt l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp' (((m1, PreTermFloat16 l1), (m2, PreTermFloat16 l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp' (((m1, PreTermFloat32 l1), (m2, PreTermFloat32 l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp' (((m1, PreTermFloat64 l1), (m2, PreTermFloat64 l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp' (((m1, PreTermFloat l1), (m2, PreTermFloat16 l2)):cs)
  | show l1 == show l2 = simpMetaRet [(m1, m2)] (simp cs)
simp' (((m1, PreTermFloat16 l1), (m2, PreTermFloat l2)):cs)
  | show l1 == show l2 = simpMetaRet [(m1, m2)] (simp cs)
simp' (((m1, PreTermFloat l1), (m2, PreTermFloat32 l2)):cs)
  | show l1 == show l2 = simpMetaRet [(m1, m2)] (simp cs)
simp' (((m1, PreTermFloat32 l1), (m2, PreTermFloat l2)):cs)
  | show l1 == show l2 = simpMetaRet [(m1, m2)] (simp cs)
simp' (((m1, PreTermFloat l1), (m2, PreTermFloat64 l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp' (((m1, PreTermFloat64 l1), (m2, PreTermFloat l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp' (((m1, PreTermFloat l1), (m2, PreTermFloat l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp' (((m1, PreTermEnum l1), (m2, PreTermEnum l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp' (((m1, PreTermEnumIntro l1), (m2, PreTermEnumIntro l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp' (((m1, PreTermArray k1 indexType1), (m2, PreTermArray k2 indexType2)):cs)
  | k1 == k2 = simpMetaRet [(m1, m2)] $ simp $ (indexType1, indexType2) : cs
simp' (((m1, PreTermArrayIntro k1 les1), (m2, PreTermArrayIntro k2 les2)):cs)
  | k1 == k2 = do
    csArray <- simpArrayIntro les1 les2
    csCont <- simpMetaRet [(m1, m2)] $ simp cs
    return $ csArray ++ csCont
simp' ((e1, e2):cs) = do
  let ms1 = asStuckedTerm e1
  let ms2 = asStuckedTerm e2
  -- ここのcategorizeはけっこうデリケートかもしれない。
  case (ms1, ms2) of
    (Just (StuckPiElimStrict h1 exs1), _) -> do
      simpStuckStrict h1 exs1 e1 e2 cs
    (_, Just (StuckPiElimStrict h2 exs2)) -> do
      simpStuckStrict h2 exs2 e2 e1 cs
    (Just (StuckHole h1), Nothing) -> do
      simpHole h1 e1 e2 cs
    (Nothing, Just (StuckHole h2)) -> do
      simpHole h2 e2 e1 cs
    (Just (StuckPiElim h1 ies1), Nothing) -> do
      simpFlexRigid h1 ies1 e1 e2 cs
    (Nothing, Just (StuckPiElim h2 ies2)) -> do
      simpFlexRigid h2 ies2 e2 e1 cs
    (Just (StuckPiElim h1 ies1), Just (StuckPiElim h2 ies2)) -> do
      simpFlexFlex h1 h2 ies1 ies2 e1 e2 cs
    _ -> simpOther e1 e2 cs

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
     PreMeta
  -> [(Identifier, PreTermPlus)]
  -> PreTermPlus
  -> PreMeta
  -> [(Identifier, PreTermPlus)]
  -> PreTermPlus
  -> [(PreTermPlus, PreTermPlus)]
  -> WithEnv [EnrichedConstraint]
simpPi m1 [] cod1 m2 [] cod2 cs =
  simpMetaRet [(m1, m2)] $ simp $ (cod1, cod2) : cs
simpPi m1 ((x1, t1):xts1) cod1 m2 ((x2, t2):xts2) cod2 cs = do
  var1 <- toVar x1 t1
  let m = metaTerminal
  let (xts2', cod2') = substPreTermPlusBindingsWithBody [(x2, var1)] xts2 cod2
  cst <- simp [(t1, t2)]
  cs' <- simpMetaRet [(m1, m2)] $ simpPi m xts1 cod1 m xts2' cod2' cs -- let tPi1 = (m, PreTermPi xts1 cod1)
  return $ cst ++ cs'
simpPi _ _ _ _ _ _ _ = throwError "simpPi"

simpHole ::
     Hole
  -> PreTermPlus
  -> PreTermPlus
  -> [PreConstraint]
  -> WithEnv [EnrichedConstraint]
simpHole h1 e1 e2 cs
  | h1 `notElem` holePreTermPlus e2
  , null (varPreTermPlus e2) = do
    cs' <- simpMetaRet [(fst e1, fst e2)] $ simp cs
    return $ Enriched (e1, e2) [h1] (ConstraintImmediate h1 e2) : cs'
  | otherwise = simpOther e1 e2 cs

simpStuckStrict ::
     Identifier
  -> [[(PreTermPlus, Identifier)]]
  -> PreTermPlus
  -> PreTermPlus
  -> [(PreTermPlus, PreTermPlus)]
  -> WithEnv [EnrichedConstraint]
simpStuckStrict h1 exs1 e1 e2 cs
  | h1 `notElem` holePreTermPlus e2
  , xs <- concat $ map (map snd) exs1
  , all (\y -> y `elem` xs) (varPreTermPlus e2) = do
    let es1 = map (map fst) exs1
    cs' <- simpMetaRet [(fst e1, fst e2)] $ simp cs
    if isDisjoint xs
      then return $ Enriched (e1, e2) [h1] (ConstraintPattern h1 es1 e2) : cs'
      else return $
           Enriched (e1, e2) [h1] (ConstraintQuasiPattern h1 es1 e2) : cs'
  | otherwise = simpOther e1 e2 cs

isDisjoint :: [Identifier] -> Bool
isDisjoint xs = xs == nub xs

getVarList :: [PreTermPlus] -> [Identifier]
getVarList xs = catMaybes $ map asUpsilon xs

simpFlexRigid ::
     Hole
  -> [[PreTermPlus]]
  -> PreTermPlus
  -> PreTermPlus
  -> [PreConstraint]
  -> WithEnv [EnrichedConstraint]
simpFlexRigid h1 ies1 e1 e2 cs
  | h1 `notElem` holePreTermPlus e2
  , xs <- concatMap getVarList ies1
  , all (\y -> y `elem` xs) (varPreTermPlus e2) = do
    cs' <- simpMetaRet [(fst e1, fst e2)] $ simp cs
    let c = Enriched (e1, e2) [h1] $ ConstraintFlexRigid h1 ies1 e2
    return $ c : cs'
simpFlexRigid _ _ e1 e2 cs = simpOther e1 e2 cs

simpFlexFlex ::
     Hole
  -> Hole
  -> [[PreTermPlus]]
  -> [[PreTermPlus]]
  -> PreTermPlus
  -> PreTermPlus
  -> [PreConstraint]
  -> WithEnv [EnrichedConstraint]
simpFlexFlex h1 h2 ies1 _ e1 e2 cs
  | h1 `notElem` holePreTermPlus e2
  , xs <- concatMap getVarList ies1
  , all (\y -> y `elem` xs) (varPreTermPlus e2) = do
    cs' <- simpMetaRet [(fst e1, fst e2)] $ simp cs
    let c = Enriched (e1, e2) [h1, h2] $ ConstraintFlexFlex h1 ies1 e2
    return $ c : cs'
simpFlexFlex h1 h2 _ ies2 e1 e2 cs
  | h2 `notElem` holePreTermPlus e1
  , xs <- concatMap getVarList ies2
  , all (\y -> y `elem` xs) (varPreTermPlus e1) = do
    cs' <- simpMetaRet [(fst e2, fst e1)] $ simp cs
    let c = Enriched (e2, e1) [h2, h1] $ ConstraintFlexFlex h2 ies2 e1
    return $ c : cs'
simpFlexFlex _ _ _ _ e1 e2 cs = simpOther e1 e2 cs

simpOther ::
     PreTermPlus
  -> PreTermPlus
  -> [PreConstraint]
  -> WithEnv [EnrichedConstraint]
simpOther e1 e2 cs = do
  cs' <- simpMetaRet [(fst e1, fst e2)] $ simp cs
  let fmvs = concatMap holePreTermPlus [e1, e2]
  let c = Enriched (e1, e2) fmvs $ ConstraintOther
  return $ c : cs'

simpMetaRet ::
     [(PreMeta, PreMeta)]
  -> WithEnv [EnrichedConstraint]
  -> WithEnv [EnrichedConstraint]
simpMetaRet mms comp = do
  cs1 <- concat <$> mapM (\(m1, m2) -> simpMeta m1 m2) mms
  cs2 <- comp
  return $ cs1 ++ cs2

simpMeta :: PreMeta -> PreMeta -> WithEnv [EnrichedConstraint]
simpMeta (PreMetaTerminal _) (PreMetaTerminal _) = return []
simpMeta (PreMetaTerminal _) m2@(PreMetaNonTerminal _ _) = do
  simpMeta (PreMetaNonTerminal univ Nothing) m2
simpMeta m1@(PreMetaNonTerminal _ _) (PreMetaTerminal _) =
  simpMeta m1 (PreMetaNonTerminal univ Nothing)
simpMeta (PreMetaNonTerminal t1 _) (PreMetaNonTerminal t2 _) = do
  simp [(t1, t2)]

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

data Stuck
  = StuckHole Hole
  | StuckPiElim Hole [[PreTermPlus]]
  | StuckPiElimStrict Hole [[(PreTermPlus, Identifier)]]

-- a stucked term is a term that cannot be evaluated due to unresolved holes.
asStuckedTerm :: PreTermPlus -> Maybe Stuck
asStuckedTerm (_, PreTermPiElim e es)
  | Just xs <- mapM asUpsilon es =
    case asStuckedTerm e of
      Just (StuckHole h) -> Just $ StuckPiElimStrict h [zip es xs]
      Just (StuckPiElim h iess) -> Just $ StuckPiElim h (iess ++ [es])
      Just (StuckPiElimStrict h iexss) ->
        Just $ StuckPiElimStrict h $ iexss ++ [zip es xs]
      Nothing -> Nothing
asStuckedTerm (_, PreTermPiElim e es) =
  case asStuckedTerm e of
    Just (StuckHole h) -> Just $ StuckPiElim h [es]
    Just (StuckPiElim h iess) -> Just $ StuckPiElim h $ iess ++ [es]
    Just (StuckPiElimStrict h exss) -> do
      let ess = map (map fst) exss
      Just $ StuckPiElim h $ ess ++ [es]
    Nothing -> Nothing
asStuckedTerm (_, PreTermZeta h) = Just $ StuckHole h
asStuckedTerm _ = Nothing

toVar :: Identifier -> PreTermPlus -> WithEnv PreTermPlus
toVar x t = return (PreMetaNonTerminal t Nothing, PreTermUpsilon x)

asUpsilon :: PreTermPlus -> Maybe Identifier
asUpsilon (_, PreTermUpsilon x) = Just x
asUpsilon _ = Nothing
