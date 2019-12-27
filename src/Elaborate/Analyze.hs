module Elaborate.Analyze
  ( analyze
  ) where

import Control.Monad.Except
import Data.List
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
  | isReducible e1 = do
    me1' <- reducePreTermPlus e1 >>= liftIO . timeout 5000000 . return
    case me1' of
      Just e1' -> simp $ (e1', e2) : cs
      Nothing ->
        throwError $ "cannot simplify [TIMEOUT]:\n" ++ Pr.ppShow (e1, e2)
simp ((e1, e2):cs)
  | isReducible e2 = simp $ (e2, e1) : cs
simp (((m1, PreTermTau), (m2, PreTermTau)):cs) =
  simpMetaRet [(m1, m2)] (simp cs)
simp (((m1, PreTermTheta x), (m2, PreTermTheta y)):cs)
  | x == y = simpMetaRet [(m1, m2)] (simp cs)
simp (((m1, PreTermUpsilon x1), (m2, PreTermUpsilon x2)):cs)
  | x1 == x2 = simpMetaRet [(m1, m2)] (simp cs)
simp (((m1, PreTermPi [] cod1), (m2, PreTermPi [] cod2)):cs) =
  simpMetaRet [(m1, m2)] $ simp $ (cod1, cod2) : cs
simp (((m1, PreTermPi ((x1, t1):xts1) cod1), (m2, PreTermPi ((x2, t2):xts2) cod2)):cs) = do
  var1 <- toVar x1 t1
  let m = metaTerminal
  let (xts2', cod2') = substPreTermPlusBindingsWithBody [(x2, var1)] xts2 cod2
  let tPi1 = (m, PreTermPi xts1 cod1)
  let tPi2 = (m, PreTermPi xts2' cod2')
  simpMetaRet [(m1, m2)] $ simp $ (t1, t2) : (tPi1, tPi2) : cs
simp (((m1, PreTermPiIntro xts1 e1), (m2, PreTermPiIntro xts2 e2)):cs) =
  simp $ ((m1, PreTermPi xts1 e1), (m2, PreTermPi xts2 e2)) : cs
simp (((m1, PreTermPiIntro xts body1), e2@(m2, _)):cs) = do
  vs <- mapM (uncurry toVar) xts
  let appMeta = (PreMetaNonTerminal (typeOf body1) Nothing)
  simpMetaRet [(m1, m2)] $ simp $ (body1, (appMeta, PreTermPiElim e2 vs)) : cs
simp ((e1, e2@(_, PreTermPiIntro {})):cs) = simp $ (e2, e1) : cs
simp (((m1, PreTermMu (x1, t1) e1), (m2, PreTermMu (x2, t2) e2)):cs)
  | x1 == x2 = simpMetaRet [(m1, m2)] $ simp $ (t1, t2) : (e1, e2) : cs
simp (((m1, PreTermZeta x), (m2, PreTermZeta y)):cs)
  | x == y = simpMetaRet [(m1, m2)] (simp cs)
simp (((m1, PreTermIntS size1 l1), (m2, PreTermIntS size2 l2)):cs)
  | size1 == size2
  , l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp (((m1, PreTermIntU size1 l1), (m2, PreTermIntU size2 l2)):cs)
  | size1 == size2
  , l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp (((m1, PreTermInt l1), (m2, PreTermIntS _ l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp (((m1, PreTermIntS _ l1), (m2, PreTermInt l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp (((m1, PreTermInt l1), (m2, PreTermIntU _ l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp (((m1, PreTermIntU _ l1), (m2, PreTermInt l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp (((m1, PreTermInt l1), (m2, PreTermInt l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp (((m1, PreTermFloat16 l1), (m2, PreTermFloat16 l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp (((m1, PreTermFloat32 l1), (m2, PreTermFloat32 l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp (((m1, PreTermFloat64 l1), (m2, PreTermFloat64 l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp (((m1, PreTermFloat l1), (m2, PreTermFloat16 l2)):cs)
  | show l1 == show l2 = simpMetaRet [(m1, m2)] (simp cs)
simp (((m1, PreTermFloat16 l1), (m2, PreTermFloat l2)):cs)
  | show l1 == show l2 = simpMetaRet [(m1, m2)] (simp cs)
simp (((m1, PreTermFloat l1), (m2, PreTermFloat32 l2)):cs)
  | show l1 == show l2 = simpMetaRet [(m1, m2)] (simp cs)
simp (((m1, PreTermFloat32 l1), (m2, PreTermFloat l2)):cs)
  | show l1 == show l2 = simpMetaRet [(m1, m2)] (simp cs)
simp (((m1, PreTermFloat l1), (m2, PreTermFloat64 l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp (((m1, PreTermFloat64 l1), (m2, PreTermFloat l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp (((m1, PreTermFloat l1), (m2, PreTermFloat l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp (((m1, PreTermEnum l1), (m2, PreTermEnum l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp (((m1, PreTermEnumIntro l1), (m2, PreTermEnumIntro l2)):cs)
  | l1 == l2 = simpMetaRet [(m1, m2)] (simp cs)
simp (((m1, PreTermArray k1 dom1 cod1), (m2, PreTermArray k2 dom2 cod2)):cs)
  | k1 == k2 = simpMetaRet [(m1, m2)] $ simp $ (dom1, dom2) : (cod1, cod2) : cs
simp (((m1, PreTermArrayIntro k1 les1), (m2, PreTermArrayIntro k2 les2)):cs)
  | k1 == k2 = do
    csArray <- simpArrayIntro les1 les2
    csCont <- simpMetaRet [(m1, m2)] $ simp cs
    return $ csArray ++ csCont
simp ((e1, e2):cs)
  | (m1, PreTermArrayElim k1 (_, PreTermUpsilon f) eps1) <- e1
  , (m2, PreTermArrayElim k2 (_, PreTermUpsilon g) eps2) <- e2
  , k1 == k2
  , f == g = simpMetaRet [(m1, m2)] $ simp $ (eps1, eps2) : cs
simp ((e1, e2):cs)
  | (m11, PreTermPiElim (m12, PreTermUpsilon f) es1) <- e1
  , (m21, PreTermPiElim (m22, PreTermUpsilon g) es2) <- e2
  , f == g
  , length es1 == length es2 =
    simpMetaRet [(m11, m21), (m12, m22)] $ simp $ zip es1 es2 ++ cs
simp ((e1, e2):cs)
  | (m11, PreTermPiElim (m12, PreTermTheta f) es1) <- e1
  , (m21, PreTermPiElim (m22, PreTermTheta g) es2) <- e2
  , f == g
  , length es1 == length es2 =
    simpMetaRet [(m11, m21), (m12, m22)] $ simp $ zip es1 es2 ++ cs
simp ((e1, e2):cs)
  | (m11, PreTermPiElim (m12, PreTermZeta f) es1) <- e1
  , (m21, PreTermPiElim (m22, PreTermZeta g) es2) <- e2
  , f == g
  , length es1 == length es2 =
    simpMetaRet [(m11, m21), (m12, m22)] $ simp $ zip es1 es2 ++ cs
simp ((e1, e2):cs) = do
  let ms1 = asStuckedTerm e1
  let ms2 = asStuckedTerm e2
  let (_, fmvs1) = varPreTermPlus e1
  let (_, fmvs2) = varPreTermPlus e2
  case (ms1, ms2) of
    (Just (StuckHole h1), _) -> simpHole h1 fmvs1 fmvs2 e1 e2 cs
    (_, Just (StuckHole h2)) -> simpHole h2 fmvs2 fmvs1 e2 e1 cs
    (Just (StuckPiElimStrict h1 exs1), _) ->
      simpStuckStrict h1 exs1 $ (e1, e2) : cs
    (_, Just (StuckPiElimStrict h2 exs2)) ->
      simpStuckStrict h2 exs2 $ (e2, e1) : cs
    (Just (StuckPiElim h1 ies1), Nothing) ->
      simpFlexRigid fmvs1 fmvs2 h1 ies1 e1 e2 cs
    (Nothing, Just (StuckPiElim h2 ies2)) ->
      simpFlexRigid fmvs2 fmvs1 h2 ies2 e2 e1 cs
    (Just (StuckPiElim h1 ies1), Just (StuckPiElim h2 _)) ->
      simpFlexFlex fmvs1 fmvs2 h1 h2 ies1 e1 e2 cs
    _ -> simpOther (fmvs1 ++ fmvs2) e1 e2 cs

simpHole ::
     Hole
  -> [Hole]
  -> [Hole]
  -> (PreMeta, PreTerm)
  -> (PreMeta, PreTerm)
  -> [PreConstraint]
  -> WithEnv [EnrichedConstraint]
simpHole h1 fmvs1 fmvs2 e1 e2 cs
  | h1 `notElem` fmvs2 = do
    cs' <- simpMetaRet [(fst e1, fst e2)] $ simp cs
    let fmvs = fmvs1 ++ fmvs2
    return $ Enriched (e1, e2) fmvs (ConstraintImmediate h1 e2) : cs'
  | otherwise = simpOther (fmvs1 ++ fmvs2) e1 e2 cs

simpStuckStrict ::
     Identifier
  -> [[(PreTermPlus, Identifier)]]
  -> [(PreTermPlus, PreTermPlus)]
  -> WithEnv [EnrichedConstraint]
simpStuckStrict _ _ [] = return []
simpStuckStrict h1 exs1 ((e1, e2):cs) = do
  let es1 = map (map fst) exs1
  cs' <- simpMetaRet [(fst e1, fst e2)] $ simp cs
  if all (isSolvable e2 h1) (map (map snd) exs1)
    then return $ Enriched (e1, e2) [h1] (ConstraintPattern h1 es1 e2) : cs'
    else return $
         Enriched (e1, e2) [h1] (ConstraintQuasiPattern h1 es1 e2) : cs'

simpFlexRigid ::
     [Hole]
  -> [Hole]
  -> Hole
  -> [[PreTermPlus]]
  -> (PreMeta, PreTerm)
  -> (PreMeta, PreTerm)
  -> [PreConstraint]
  -> WithEnv [EnrichedConstraint]
simpFlexRigid _ fmvs2 h1 ies1 e1 e2 cs
  | h1 `notElem` fmvs2 = do
    cs' <- simpMetaRet [(fst e1, fst e2)] $ simp cs
    let c = Enriched (e1, e2) [h1] $ ConstraintFlexRigid h1 ies1 e2
    return $ c : cs'
simpFlexRigid fmvs1 fmvs2 _ _ e1 e2 cs = simpOther (fmvs1 ++ fmvs2) e1 e2 cs

simpFlexFlex ::
     [Hole]
  -> [Hole]
  -> Hole
  -> Hole
  -> [[PreTermPlus]]
  -> (PreMeta, PreTerm)
  -> (PreMeta, PreTerm)
  -> [PreConstraint]
  -> WithEnv [EnrichedConstraint]
simpFlexFlex _ fmvs2 h1 h2 ies1 e1 e2 cs
  | h1 `notElem` fmvs2 = do
    cs' <- simpMetaRet [(fst e1, fst e2)] $ simp cs
    let c = Enriched (e1, e2) [h1, h2] $ ConstraintFlexFlex h1 ies1 e2
    return $ c : cs'
simpFlexFlex fmvs1 fmvs2 _ _ _ e1 e2 cs = simpOther (fmvs1 ++ fmvs2) e1 e2 cs

simpOther ::
     [Hole]
  -> PreTermPlus
  -> PreTermPlus
  -> [PreConstraint]
  -> WithEnv [EnrichedConstraint]
simpOther fmvs e1 e2 cs = do
  cs' <- simpMetaRet [(fst e1, fst e2)] $ simp cs
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
  | Just xs <- mapM interpretAsUpsilon es =
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

isSolvable :: PreTermPlus -> Identifier -> [Identifier] -> Bool
isSolvable e x xs = do
  let (fvs, fmvs) = varPreTermPlus e
  affineCheck xs fvs && x `notElem` fmvs

toVar :: Identifier -> PreTermPlus -> WithEnv PreTermPlus
toVar x t = return (PreMetaNonTerminal t Nothing, PreTermUpsilon x)

affineCheck :: [Identifier] -> [Identifier] -> Bool
affineCheck xs = affineCheck' xs xs

affineCheck' :: [Identifier] -> [Identifier] -> [Identifier] -> Bool
affineCheck' _ [] _ = True
affineCheck' xs (y:ys) fvs =
  if y `notElem` fvs
    then affineCheck' xs ys fvs
    else isLinear y xs && affineCheck' xs ys fvs

isLinear :: Identifier -> [Identifier] -> Bool
isLinear x xs = length (filter (== x) xs) == 1

interpretAsUpsilon :: PreTermPlus -> Maybe Identifier
interpretAsUpsilon (_, PreTermUpsilon x) = Just x
interpretAsUpsilon _ = Nothing
