module Elaborate.Analyze
  ( analyze
  , simp
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
import Elaborate.Infer (typeOf, univ)
import Reduce.PreTerm

analyze :: [PreConstraint] -> WithEnv ConstraintQueue
analyze cs = Q.fromList <$> simp cs

simp :: [PreConstraint] -> WithEnv [EnrichedConstraint]
simp [] = return []
simp ((e1, e2):cs)
  | isReducible e1 = do
    me1' <-
      reducePreTermPlus e1 >>= \e1' -> liftIO $ timeout 5000000 $ return e1'
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
simp (((m1, PreTermPi xts1 cod1), (m2, PreTermPi xts2 cod2)):cs)
  | length xts1 == length xts2 =
    simpMetaRet [(m1, m2)] $ simpBinder xts1 cod1 xts2 cod2 cs
simp (((m1, PreTermPiIntro xts1 e1), (m2, PreTermPiIntro xts2 e2)):cs)
  | length xts1 == length xts2 =
    simpMetaRet [(m1, m2)] $ simpBinder xts1 e1 xts2 e2 cs
simp (((m1, PreTermPiIntro xts body1), e2@(m2, _)):cs) = do
  vs <- mapM (uncurry toVar) xts
  let appMeta = (PreMetaNonTerminal (typeOf body1) Nothing)
  let comp = simp $ (body1, (appMeta, PreTermPiElim e2 vs)) : cs
  simpMetaRet [(m1, m2)] comp
simp ((e1, e2@(_, PreTermPiIntro {})):cs) = simp $ (e2, e1) : cs
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
simp ((e1, e2):cs) = do
  let ms1 = asStuckedTerm e1
  let ms2 = asStuckedTerm e2
  let (_, fmvs1) = varPreTermPlus e1
  let (_, fmvs2) = varPreTermPlus e2
  case (ms1, ms2) of
    (Just (StuckHole h), _)
      | h `notElem` fmvs2 -> do
        cs' <- simpMetaRet [(fst e1, fst e2)] $ simp cs
        return $ Enriched (e1, e2) [h] (ConstraintImmediate h e2) : cs'
    (_, Just (StuckHole h))
      | h `notElem` fmvs1 -> simp $ (e2, e1) : cs
    (Just (StuckPiElimStrict h1 exs1), _) ->
      simpPatIfPossible ms1 ms2 h1 exs1 $ (e1, e2) : cs
    (_, Just (StuckPiElimStrict h2 exs2)) ->
      simpPatIfPossible ms2 ms1 h2 exs2 $ (e2, e1) : cs
    _ -> simpStuck ms1 ms2 $ (e1, e2) : cs

simpPatIfPossible ::
     Maybe Stuck
  -> Maybe Stuck
  -> Identifier
  -> [[(PreTermPlus, Identifier)]]
  -> [((PreMeta, PreTerm), PreTermPlus)]
  -> WithEnv [EnrichedConstraint]
simpPatIfPossible _ _ _ _ [] = return []
simpPatIfPossible ms1 ms2 h1 exs1 ((e1, e2):cs) = do
  isPattern <- allM (isSolvable e2 h1) (map (map snd) exs1)
  if isPattern
    then do
      cs' <- simpMetaRet [(fst e1, fst e2)] $ simp cs
      let es1 = map (map fst) exs1
      return $ Enriched (e1, e2) [h1] (ConstraintPattern h1 es1 e2) : cs'
    else simpStuck ms1 ms2 $ (e1, e2) : cs

simpStuck ::
     Maybe Stuck
  -> Maybe Stuck
  -> [((PreMeta, PreTerm), (PreMeta, PreTerm))]
  -> WithEnv [EnrichedConstraint]
simpStuck _ _ [] = return []
simpStuck ms1 ms2 ((e1, e2):cs) =
  case (ms1, ms2) of
    (Just (StuckPiElimStrict h1 exs1), _) -> do
      cs' <- simpMetaRet [(fst e1, fst e2)] $ simp cs
      let es1 = map (map fst) exs1
      return $ Enriched (e1, e2) [h1] (ConstraintQuasiPattern h1 es1 e2) : cs'
    (_, Just StuckPiElimStrict {}) -> simpStuck ms2 ms1 $ (e2, e1) : cs
    (Just (StuckPiElim h1 ies1), Nothing) -> do
      cs' <- simpMetaRet [(fst e1, fst e2)] $ simp cs
      let c = Enriched (e1, e2) [h1] $ ConstraintFlexRigid h1 ies1 e2
      return $ c : cs'
    (Nothing, Just StuckPiElim {}) -> simpStuck ms2 ms1 $ (e2, e1) : cs
    (Just (StuckPiElim h1 ies1), Just (StuckPiElim h2 _)) -> do
      cs' <- simpMetaRet [(fst e1, fst e2)] $ simp cs
      let c = Enriched (e1, e2) [h1, h2] $ ConstraintFlexFlex h1 ies1 e2
      return $ c : cs'
    _ -> throwError $ "cannot simplify:\n" ++ Pr.ppShow (e1, e2) -- ここでcsについても処理をおこなうと複数のエラーを検出できる

simpMetaRet ::
     [(PreMeta, PreMeta)]
  -> WithEnv [EnrichedConstraint]
  -> WithEnv [EnrichedConstraint]
simpMetaRet mms comp = do
  cs1 <- mapM (\(m1, m2) -> simpMeta m1 m2) mms
  cs2 <- comp
  return $ concat cs1 ++ cs2

simpMeta :: PreMeta -> PreMeta -> WithEnv [EnrichedConstraint]
simpMeta (PreMetaTerminal _) (PreMetaTerminal _) = return []
simpMeta (PreMetaTerminal _) m2@(PreMetaNonTerminal _ _) = do
  simpMeta (PreMetaNonTerminal univ Nothing) m2
simpMeta m1@(PreMetaNonTerminal _ _) (PreMetaTerminal _) =
  simpMeta m1 (PreMetaNonTerminal univ Nothing)
simpMeta (PreMetaNonTerminal t1 _) (PreMetaNonTerminal t2 _) = do
  simp [(t1, t2)]

simpBinder ::
     [IdentifierPlus]
  -> PreTermPlus
  -> [IdentifierPlus]
  -> PreTermPlus
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
  let s = substPreTermPlus (zip (map fst xts2) vs1')
  let xts2' = map (s . snd) xts2
  simp $ zip (map snd xts1) xts2' ++ cs

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

isSolvable :: PreTermPlus -> Identifier -> [Identifier] -> WithEnv Bool
isSolvable e x xs = do
  let (fvs, fmvs) = varPreTermPlus e
  return $ affineCheck xs fvs && x `notElem` fmvs

toVar :: Identifier -> PreTermPlus -> WithEnv PreTermPlus
toVar x t = return (PreMetaNonTerminal t Nothing, PreTermUpsilon x)

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

interpretAsUpsilon :: PreTermPlus -> Maybe Identifier
interpretAsUpsilon (_, PreTermUpsilon x) = Just x
interpretAsUpsilon _ = Nothing

allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM _ [] = return True
allM f (x:xs) = do
  b1 <- f x
  b2 <- allM f xs
  return $ b1 && b2
