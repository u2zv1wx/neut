{-# LANGUAGE OverloadedStrings #-}

module Elaborate.Analyze
  ( analyze
  , simp
  , toPiElim
  , linearCheck
  , unfoldIter
  , toVarList
  , bindFormalArgs
  , lookupAny
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.Maybe
import System.Timeout

import qualified Data.HashMap.Strict as Map
import qualified Data.PQueue.Min as Q
import qualified Data.Text as T
import qualified Text.Show.Pretty as Pr

import Data.Basic
import Data.Constraint
import Data.Env
import Data.WeakTerm
import Reduce.WeakTerm

analyze :: WithEnv ()
analyze = do
  cs <- gets constraintEnv
  simp cs

simp :: [PreConstraint] -> WithEnv ()
simp [] = return ()
simp ((e1, e2):cs) = do
  me1' <- return (reduceWeakTermPlus e1) >>= liftIO . timeout 5000000 . return
  me2' <- return (reduceWeakTermPlus e2) >>= liftIO . timeout 5000000 . return
  case (me1', me2') of
    (Just e1', Just e2') -> simp' $ (e1', e2') : cs
    _ ->
      throwError' $
      "cannot simplify [TIMEOUT]:\n" <> T.pack (Pr.ppShow (e1, e2))

simp' :: [PreConstraint] -> WithEnv ()
simp' [] = return ()
simp' (((_, e1), (_, e2)):cs)
  | e1 == e2 = simp cs
simp' (((m1, WeakTermTau l1), (m2, WeakTermTau l2)):cs) = do
  lenv <- gets levelEnv
  let ml1 = UnivLevelPlus (m1, l1)
  let ml2 = UnivLevelPlus (m2, l2)
  modify (\env -> env {levelEnv = substLevelConstraint ml1 ml2 lenv})
  simp cs
simp' (((_, WeakTermPi mls1 xts1 cod1), (_, WeakTermPi mls2 xts2 cod2)):cs)
  | length xts1 == length xts2 = do
    let us1 = map asUniv mls1
    let us2 = map asUniv mls2
    simpBinder xts1 xts2 (Just (cod1, cod2)) $ zip us1 us2 ++ cs
simp' (((_, WeakTermPiIntro xts1 e1), (_, WeakTermPiIntro xts2 e2)):cs)
  | length xts1 == length xts2 = simpBinder xts1 xts2 (Just (e1, e2)) cs
simp' (((_, WeakTermPiIntro xts body1@(m1, _)), e2@(_, _)):cs) = do
  let vs = map (\(_, x, _) -> toVar x) xts
  simp $ (body1, (m1, WeakTermPiElim e2 vs)) : cs
simp' ((e1, e2@(_, WeakTermPiIntro {})):cs) = simp' $ (e2, e1) : cs
simp' (((_, WeakTermSigma xts1), (_, WeakTermSigma xts2)):cs)
  | length xts1 == length xts2 = simpBinder xts1 xts2 Nothing cs
simp' (((_, WeakTermSigmaIntro t1 es1), (_, WeakTermSigmaIntro t2 es2)):cs)
  | length es1 == length es2 = simp $ (t1, t2) : zip es1 es2 ++ cs
simp' (((_, WeakTermIter xt1@(_, x1, _) xts1 e1), (_, WeakTermIter xt2@(_, x2, _) xts2 e2)):cs)
  | x1 == x2
  , length xts1 == length xts2 =
    simpBinder (xt1 : xts1) (xt2 : xts2) (Just (e1, e2)) cs
simp' (((_, WeakTermConstDecl xt1 e1), (_, WeakTermConstDecl xt2 e2)):cs) = do
  simpBinder [xt1] [xt2] (Just (e1, e2)) cs
simp' (((_, WeakTermInt t1 l1), (_, WeakTermEnumIntro (EnumValueIntS s2 l2))):cs)
  | l1 == l2 = simp $ (t1, toIntS s2) : cs
simp' (((_, WeakTermEnumIntro (EnumValueIntS s1 l1)), (_, WeakTermInt t2 l2)):cs)
  | l1 == l2 = simp $ (toIntS s1, t2) : cs
simp' (((_, WeakTermInt t1 l1), (_, WeakTermEnumIntro (EnumValueIntU s2 l2))):cs)
  | l1 == l2 = simp $ (t1, toIntU s2) : cs
simp' (((_, WeakTermEnumIntro (EnumValueIntU s1 l1)), (_, WeakTermInt t2 l2)):cs)
  | l1 == l2 = simp $ (toIntU s1, t2) : cs
simp' (((_, WeakTermInt t1 l1), (_, WeakTermInt t2 l2)):cs)
  | l1 == l2 = simp $ (t1, t2) : cs
simp' (((_, WeakTermFloat t1 l1), (_, WeakTermFloat16 l2)):cs)
  | show l1 == show l2 = simp $ (t1, f16) : cs
simp' (((_, WeakTermFloat16 l1), (_, WeakTermFloat t2 l2)):cs)
  | show l1 == show l2 = simp $ (f16, t2) : cs
simp' (((_, WeakTermFloat t1 l1), (_, WeakTermFloat32 l2)):cs)
  | show l1 == show l2 = simp $ (t1, f32) : cs
simp' (((_, WeakTermFloat32 l1), (_, WeakTermFloat t2 l2)):cs)
  | show l1 == show l2 = simp $ (f32, t2) : cs
simp' (((_, WeakTermFloat t1 l1), (_, WeakTermFloat64 l2)):cs)
  | l1 == l2 = simp $ (t1, f64) : cs
simp' (((_, WeakTermFloat64 l1), (_, WeakTermFloat t2 l2)):cs)
  | l1 == l2 = simp $ (f64, t2) : cs
simp' (((_, WeakTermFloat t1 l1), (_, WeakTermFloat t2 l2)):cs)
  | l1 == l2 = simp $ (t1, t2) : cs
simp' (((_, WeakTermArray dom1 k1), (_, WeakTermArray dom2 k2)):cs)
  | k1 == k2 = simp $ (dom1, dom2) : cs
simp' (((_, WeakTermArrayIntro k1 es1), (_, WeakTermArrayIntro k2 es2)):cs)
  | k1 == k2
  , length es1 == length es2 = simp $ zip es1 es2 ++ cs
simp' (((_, WeakTermStructIntro eks1), (_, WeakTermStructIntro eks2)):cs)
  | (es1, ks1) <- unzip eks1
  , (es2, ks2) <- unzip eks2
  , ks1 == ks2 = simp $ zip es1 es2 ++ cs
simp' ((e1, e2):cs) = do
  let ms1 = asStuckedTerm e1
  let ms2 = asStuckedTerm e2
  -- list of stuck reasons (fmvs: free meta-variables)
  let fmvs = catMaybes [ms1 >>= stuckReasonOf, ms2 >>= stuckReasonOf]
  sub <- gets substEnv
  case lookupAny fmvs sub of
    Just (h, e) -> do
      let m = supMeta (metaOf e1) (metaOf e2)
      let e1' = substWeakTermPlus [(h, e)] (m, snd e1)
      let e2' = substWeakTermPlus [(h, e)] (m, snd e2)
      simp $ (e1', e2') : cs
    Nothing -> do
      let hs1 = holeWeakTermPlus e1
      let hs2 = holeWeakTermPlus e2
      case (ms1, ms2) of
        (Just (StuckPiElimConst f1 ess1), Just (StuckPiElimConst f2 ess2))
          | f1 == f2
          , length ess1 == length ess2
          , es1 <- concat ess1
          , es2 <- concat ess2
          -- es1 = [[a, b], [c]], es2 =  [[d], [e, f]]とかを許してしまっているので修正すること
          , length es1 == length es2 -> simp $ zip es1 es2 ++ cs
        (Just (StuckPiElimIter iter1@(_, x1, _, _, _) mess1), Just (StuckPiElimIter (_, x2, _, _, _) mess2))
          | x1 == x2
          , length mess1 == length mess2
          , ess1 <- map snd mess1
          , ess2 <- map snd mess2
          , length (concat ess1) == length (concat ess2) -> do
            let c = Enriched (e1, e2) [] $ ConstraintDelta iter1 mess1 mess2
            insConstraintQueue c
            simp cs
        (Just (StuckPiElimIter iter1 mess1), Just (StuckPiElimIter iter2 mess2)) -> do
          let e1' = toPiElim (unfoldIter iter1) mess1
          let e2' = toPiElim (unfoldIter iter2) mess2
          simp $ (e1', e2') : cs
        (Just (StuckPiElimIter iter1 mess1), _) -> do
          simp $ (toPiElim (unfoldIter iter1) mess1, e2) : cs
        (_, Just (StuckPiElimIter iter2 mess2)) -> do
          simp $ (e1, toPiElim (unfoldIter iter2) mess2) : cs
        (Just (StuckPiElimZetaStrict h1 ies1), _)
          | xs1 <- concatMap getVarList ies1
          , occurCheck h1 hs2
          , linearCheck xs1
          , zs <- includeCheck xs1 e2
          , Just es <- lookupAll zs sub -> do
            let m = supMeta (metaOf e1) (metaOf e2)
            let e1' = (m, snd e1)
            let e2' = (m, snd e2)
            case es of
              [] -> simpPattern h1 ies1 e1' e2' cs
              _ -> simp $ (e1', substWeakTermPlus (zip zs es) e2') : cs
        (_, Just (StuckPiElimZetaStrict h2 ies2))
          | xs2 <- concatMap getVarList ies2
          , occurCheck h2 hs1
          , linearCheck xs2
          , zs <- includeCheck xs2 e1
          , Just es <- lookupAll zs sub -> do
            let m = supMeta (metaOf e1) (metaOf e2)
            let e1' = (m, snd e1)
            let e2' = (m, snd e2)
            case es of
              [] -> simpPattern h2 ies2 e2' e1' cs
              _ -> simp $ (substWeakTermPlus (zip zs es) e1', e2') : cs
        (Just (StuckPiElimUpsilon x1 _), _)
          | Just body <- Map.lookup x1 sub -> do
            let m = supMeta (supMeta (metaOf e1) (metaOf e2)) (metaOf body) -- x1 == e1 == body
            let e1' = (m, snd e1)
            let e2' = (m, snd e2)
            let body' = (m, snd body)
            simp $ (substWeakTermPlus [(x1, body')] e1', e2') : cs
        (_, Just (StuckPiElimUpsilon x2 _))
          | Just body <- Map.lookup x2 sub -> do
            let m = supMeta (supMeta (metaOf e1) (metaOf e2)) (metaOf body) -- x2 == e2 == body
            let e1' = (m, snd e1)
            let e2' = (m, snd e2)
            let body' = (m, snd body)
            simp $ (e1', substWeakTermPlus [(x2, body')] e2') : cs
        (Just (StuckPiElimUpsilon x1 ess1), Just (StuckPiElimUpsilon x2 ess2))
          | x1 == x2
          , length ess1 == length ess2
          , es1 <- concat ess1
          , es2 <- concat ess2
          -- es1 = [[a, b], [c]], es2 =  [[d], [e, f]]とかを許してしまっているので修正すること
          , length es1 == length es2 -> simp $ zip es1 es2 ++ cs
        (Just (StuckPiElimZetaStrict h1 ies1), _)
          | xs1 <- concatMap getVarList ies1
          , occurCheck h1 hs2
          , zs <- includeCheck xs1 e2
          , Just es <- lookupAll zs sub -> do
            let m = supMeta (metaOf e1) (metaOf e2)
            let e1' = (m, snd e1)
            let e2' = (m, snd e2)
            case es of
              [] -> simpQuasiPattern h1 ies1 e1' e2' fmvs cs
              _ -> simp $ (e1', substWeakTermPlus (zip zs es) e2') : cs
        (_, Just (StuckPiElimZetaStrict h2 ies2))
          | xs2 <- concatMap getVarList ies2
          , occurCheck h2 hs1
          , zs <- includeCheck xs2 e1
          , Just es <- lookupAll zs sub -> do
            let m = supMeta (metaOf e1) (metaOf e2)
            let e1' = (m, snd e1)
            let e2' = (m, snd e2)
            case es of
              [] -> simpQuasiPattern h2 ies2 e2' e1' fmvs cs
              _ -> simp $ (substWeakTermPlus (zip zs es) e1', e2') : cs
        (Just (StuckPiElimZeta h1 ies1), Nothing)
          | xs1 <- concatMap getVarList ies1
          , occurCheck h1 hs2
          , [] <- includeCheck xs1 e2 -> do
            let m = supMeta (metaOf e1) (metaOf e2)
            let e1' = (m, snd e1)
            let e2' = (m, snd e2)
            simpFlexRigid h1 ies1 e1' e2' fmvs cs
        (Nothing, Just (StuckPiElimZeta h2 ies2))
          | xs2 <- concatMap getVarList ies2
          , occurCheck h2 hs1
          , [] <- includeCheck xs2 e1 -> do
            let m = supMeta (metaOf e1) (metaOf e2)
            let e1' = (m, snd e1)
            let e2' = (m, snd e2)
            simpFlexRigid h2 ies2 e2' e1' fmvs cs
        _ -> simpOther e1 e2 fmvs cs

-- {} simpBinder {}
simpBinder ::
     [IdentifierPlus]
  -> [IdentifierPlus]
  -> Maybe (WeakTermPlus, WeakTermPlus)
  -> [(WeakTermPlus, WeakTermPlus)]
  -> WithEnv ()
simpBinder [] [] Nothing cs = simp cs
simpBinder [] [] (Just (cod1, cod2)) cs = simp $ (cod1, cod2) : cs
simpBinder ((_, x1, t1):xts1) ((_, x2, t2):xts2) Nothing cs = do
  let var1 = toVar x1
  let xts2' = substWeakTermPlusBindings [(x2, var1)] xts2
  simp [(t1, t2)]
  simpBinder xts1 xts2' Nothing cs
simpBinder ((_, x1, t1):xts1) ((_, x2, t2):xts2) (Just (cod1, cod2)) cs = do
  let var1 = toVar x1
  let (xts2', cod2') = substWeakTermPlusBindingsWithBody [(x2, var1)] xts2 cod2
  simp [(t1, t2)]
  simpBinder xts1 xts2' (Just (cod1, cod2')) cs
simpBinder _ _ _ _ = throwError' "cannot simplify (simpBinder)"

-- {} simpPattern {}
simpPattern ::
     Identifier
  -> [[WeakTermPlus]]
  -> WeakTermPlus
  -> WeakTermPlus
  -> [PreConstraint]
  -> WithEnv ()
simpPattern h1 ies1 _ e2 cs = do
  xss <- mapM toVarList ies1
  let lam = bindFormalArgs e2 xss
  modify (\env -> env {substEnv = Map.insert h1 lam (substEnv env)})
  visit h1
  simp cs

-- {} simpQuasiPattern {}
simpQuasiPattern ::
     Identifier
  -> [[WeakTermPlus]]
  -> WeakTermPlus
  -> WeakTermPlus
  -> [Identifier]
  -> [PreConstraint]
  -> WithEnv ()
simpQuasiPattern h1 ies1 e1 e2 fmvs cs = do
  insConstraintQueue $
    Enriched (e1, e2) fmvs (ConstraintQuasiPattern h1 ies1 e2)
  simp cs

-- {} simpFlexRigid {}
simpFlexRigid ::
     Hole
  -> [[WeakTermPlus]]
  -> WeakTermPlus
  -> WeakTermPlus
  -> [Identifier]
  -> [PreConstraint]
  -> WithEnv ()
simpFlexRigid h1 ies1 e1 e2 fmvs cs = do
  insConstraintQueue $ Enriched (e1, e2) fmvs (ConstraintFlexRigid h1 ies1 e2)
  simp cs

-- {} simpOther {}
simpOther ::
     WeakTermPlus -> WeakTermPlus -> [Hole] -> [PreConstraint] -> WithEnv ()
simpOther e1 e2 fmvs cs = do
  insConstraintQueue $ Enriched (e1, e2) fmvs $ ConstraintOther
  simp cs

data Stuck
  = StuckPiElimUpsilon Identifier [[WeakTermPlus]]
  | StuckPiElimZeta Identifier [[WeakTermPlus]]
  | StuckPiElimZetaStrict Identifier [[WeakTermPlus]]
  | StuckPiElimIter IterInfo [(Meta, [WeakTermPlus])]
  | StuckPiElimConst Identifier [[WeakTermPlus]]

-- {} asStuckedTerm {}
asStuckedTerm :: WeakTermPlus -> Maybe Stuck
asStuckedTerm (_, WeakTermUpsilon x) = Just $ StuckPiElimUpsilon x []
asStuckedTerm (_, WeakTermZeta h) = Just $ StuckPiElimZetaStrict h []
asStuckedTerm (_, WeakTermConst x) = Just $ StuckPiElimConst x []
asStuckedTerm self@(mi, WeakTermIter (_, x, _) xts body) =
  Just $ StuckPiElimIter (mi, x, xts, body, self) []
asStuckedTerm (m, WeakTermPiElim e es)
  | Just _ <- mapM asUpsilon es =
    case asStuckedTerm e of
      Just (StuckPiElimZeta h iess) -> Just $ StuckPiElimZeta h (iess ++ [es])
      Just (StuckPiElimZetaStrict h iexss) ->
        Just $ StuckPiElimZetaStrict h $ iexss ++ [es]
      Just (StuckPiElimIter mu ess) ->
        Just $ StuckPiElimIter mu $ ess ++ [(m, es)]
      Just (StuckPiElimConst x ess) -> Just $ StuckPiElimConst x $ ess ++ [es]
      Just (StuckPiElimUpsilon x ess) ->
        Just $ StuckPiElimUpsilon x $ ess ++ [es]
      Nothing -> Nothing
asStuckedTerm (m, WeakTermPiElim e es) =
  case asStuckedTerm e of
    Just (StuckPiElimZeta h iess) -> Just $ StuckPiElimZeta h $ iess ++ [es]
    Just (StuckPiElimZetaStrict h iess) -> do
      Just $ StuckPiElimZeta h $ iess ++ [es]
    Just (StuckPiElimIter mu ess) ->
      Just $ StuckPiElimIter mu $ ess ++ [(m, es)]
    Just (StuckPiElimConst x ess) -> Just $ StuckPiElimConst x $ ess ++ [es]
    Just (StuckPiElimUpsilon x ess) -> Just $ StuckPiElimUpsilon x $ ess ++ [es]
    Nothing -> Nothing
asStuckedTerm _ = Nothing

-- {} stuckReasonOf {}
stuckReasonOf :: Stuck -> Maybe Hole
stuckReasonOf (StuckPiElimUpsilon _ _) = Nothing
stuckReasonOf (StuckPiElimZeta h _) = Just h
stuckReasonOf (StuckPiElimZetaStrict h _) = Just h
stuckReasonOf (StuckPiElimIter {}) = Nothing
stuckReasonOf (StuckPiElimConst _ _) = Nothing

-- stuckReasonOf (StuckUpsilon _) = Nothing
-- {} occurCheck {}
occurCheck :: Identifier -> [Identifier] -> Bool
occurCheck h fmvs = h `notElem` fmvs

-- {} includeCheck {}
includeCheck :: [Identifier] -> WeakTermPlus -> [Identifier]
-- includeCheck xs e = all (`elem` xs) $ varWeakTermPlus e
includeCheck xs e = filter (`notElem` xs) $ varWeakTermPlus e

-- {} getVarList {}
getVarList :: [WeakTermPlus] -> [Identifier]
getVarList xs = catMaybes $ map asUpsilon xs

-- {} toPiElim {}
toPiElim :: WeakTermPlus -> [(Meta, [WeakTermPlus])] -> WeakTermPlus
toPiElim e [] = e
toPiElim e ((m, es):ess) = toPiElim (m, WeakTermPiElim e es) ess

unfoldIter :: IterInfo -> WeakTermPlus
unfoldIter (mi, x, xts, body, self) = do
  let m = supMeta mi (metaOf body)
  -- let body' = substWeakTermPlus [(x, self)] body
  let body' = substWeakTermPlus [(x, self)] (m, snd body)
  (fst self, WeakTermPiIntro xts body')

insConstraintQueue :: EnrichedConstraint -> WithEnv ()
insConstraintQueue c = do
  modify (\env -> env {constraintQueue = Q.insert c (constraintQueue env)})

visit :: Identifier -> WithEnv ()
visit m = do
  q <- gets constraintQueue
  let (q1, q2) = Q.partition (\(Enriched _ ms _) -> m `elem` ms) q
  modify (\env -> env {constraintQueue = q2})
  simp $ map (\(Enriched c _ _) -> c) $ Q.toList q1

-- [e, x, y, y, e2, e3, z] ~> [p, x, y, y, q, r, z]  (p, q, r: new variables)
-- {} toVarList {}
toVarList :: [WeakTermPlus] -> WithEnv [IdentifierPlus]
toVarList [] = return []
toVarList ((m, WeakTermUpsilon x):es) = do
  xts <- toVarList es
  let t = (emptyMeta, WeakTermUpsilon "_")
  return $ (m, x, t) : xts
toVarList ((m, _):es) = do
  xts <- toVarList es
  x <- newNameWith "hole"
  let t = (emptyMeta, WeakTermUpsilon "_")
  return $ (m, x, t) : xts

bindFormalArgs :: WeakTermPlus -> [[IdentifierPlus]] -> WeakTermPlus
bindFormalArgs e [] = e
bindFormalArgs e (xts:xtss) = do
  let e' = bindFormalArgs e xtss
  (emptyMeta, WeakTermPiIntro xts e')

lookupAny :: [Hole] -> Map.HashMap Identifier a -> Maybe (Hole, a)
lookupAny [] _ = Nothing
lookupAny (h:ks) sub = do
  case Map.lookup h sub of
    Just v -> Just (h, v)
    _ -> lookupAny ks sub

lookupAll :: [Identifier] -> Map.HashMap Identifier a -> Maybe [a]
lookupAll [] _ = return []
lookupAll (x:xs) sub = do
  v <- Map.lookup x sub
  vs <- lookupAll xs sub
  return $ v : vs
