{-# LANGUAGE OverloadedStrings #-}

module Elaborate.Analyze
  ( analyze
  , simp
  , toPiElim
  , unfoldIter
  , toVarList
  , bindFormalArgs
  , lookupAny
  ) where

import Control.Monad.State
import Data.Maybe

import qualified Data.IntMap.Strict as IntMap
import qualified Data.PQueue.Min as Q
import qualified Data.Set as S

import Data.Basic
import Data.Constraint
import Data.Env
import Data.Term (weaken)
import Data.WeakTerm
import Elaborate.Infer
import Reduce.WeakTerm

analyze :: WithEnv ()
analyze = do
  cs <- gets constraintEnv
  simp cs

simp :: [PreConstraint] -> WithEnv ()
simp [] = return ()
simp ((e1, e2):cs) = simp' $ (reduceWeakTermPlus e1, reduceWeakTermPlus e2) : cs

simp' :: [PreConstraint] -> WithEnv ()
simp' [] = return ()
simp' (((_, e1), (_, e2)):cs)
  | e1 == e2 = simp cs
simp' (((m1, WeakTermTau l1), (m2, WeakTermTau l2)):cs) = do
  insLevelEQ (UnivLevelPlus (m1, l1)) (UnivLevelPlus (m2, l2))
  simp cs
simp' (((m1, WeakTermPi mls1 xts1 cod1), (m2, WeakTermPi mls2 xts2 cod2)):cs)
  | length xts1 == length xts2 = do
    let us1 = map asUniv mls1
    let us2 = map asUniv mls2
    xt1 <- asIdentPlus m1 cod1
    xt2 <- asIdentPlus m2 cod2
    simpBinder (xts1 ++ [xt1]) (xts2 ++ [xt2])
    simp $ zip us1 us2 ++ cs
simp' (((m1, WeakTermPiPlus name1 mls1 xts1 cod1), (m2, WeakTermPiPlus name2 mls2 xts2 cod2)):cs)
  | name1 == name2
  , length xts1 == length xts2 = do
    let us1 = map asUniv mls1
    let us2 = map asUniv mls2
    xt1 <- asIdentPlus m1 cod1
    xt2 <- asIdentPlus m2 cod2
    simpBinder (xts1 ++ [xt1]) (xts2 ++ [xt2])
    simp $ zip us1 us2 ++ cs
simp' (((m1, WeakTermPiIntro xts1 e1), (m2, WeakTermPiIntro xts2 e2)):cs)
  | length xts1 == length xts2 = do
    xt1 <- asIdentPlus m1 e1
    xt2 <- asIdentPlus m2 e2
    simpBinder (xts1 ++ [xt1]) (xts2 ++ [xt2])
    simp cs
simp' (((m1, WeakTermPiIntroPlus ind1 (name1, args1) xts1 e1), (m2, WeakTermPiIntroPlus ind2 (name2, args2) xts2 e2)):cs)
  | ind1 == ind2
  , name1 == name2
  , length args1 == length args2 = do
    simpBinder args1 args2
    simp $ ((m1, WeakTermPiIntro xts1 e1), (m2, WeakTermPiIntro xts2 e2)) : cs
simp' (((_, WeakTermPiIntro xts body1@(m1, _)), e2@(_, _)):cs) = do
  let vs = map (\(m, x, _) -> (m, WeakTermUpsilon x)) xts
  simp $ (body1, (m1, WeakTermPiElim e2 vs)) : cs
simp' ((e1, e2@(_, WeakTermPiIntro {})):cs) = simp' $ (e2, e1) : cs
simp' (((_, WeakTermSigma xts1), (_, WeakTermSigma xts2)):cs)
  | length xts1 == length xts2 = do
    simpBinder xts1 xts2
    simp cs
simp' (((_, WeakTermSigmaIntro t1 es1), (_, WeakTermSigmaIntro t2 es2)):cs)
  | length es1 == length es2 = simp $ (t1, t2) : zip es1 es2 ++ cs
simp' (((m1, WeakTermIter xt1@(_, x1, _) xts1 e1), (m2, WeakTermIter xt2@(_, x2, _) xts2 e2)):cs)
  | x1 == x2
  , length xts1 == length xts2 = do
    yt1 <- asIdentPlus m1 e1
    yt2 <- asIdentPlus m2 e2
    simpBinder (xt1 : xts1 ++ [yt1]) (xt2 : xts2 ++ [yt2])
    simp cs
simp' (((_, WeakTermInt t1 l1), (m, WeakTermEnumIntro (EnumValueIntS s2 l2))):cs)
  | l1 == l2 = simp $ (t1, toIntS m s2) : cs
simp' (((m, WeakTermEnumIntro (EnumValueIntS s1 l1)), (_, WeakTermInt t2 l2)):cs)
  | l1 == l2 = simp $ (toIntS m s1, t2) : cs
simp' (((_, WeakTermInt t1 l1), (m, WeakTermEnumIntro (EnumValueIntU s2 l2))):cs)
  | l1 == l2 = simp $ (t1, toIntU m s2) : cs
simp' (((m, WeakTermEnumIntro (EnumValueIntU s1 l1)), (_, WeakTermInt t2 l2)):cs)
  | l1 == l2 = simp $ (toIntU m s1, t2) : cs
simp' (((_, WeakTermInt t1 l1), (_, WeakTermInt t2 l2)):cs)
  | l1 == l2 = simp $ (t1, t2) : cs
simp' (((_, WeakTermFloat t1 l1), (m2, WeakTermFloat16 l2)):cs)
  | show l1 == show l2 = do
    f16 <- lookupConstantPlus m2 "f16"
    simp $ (t1, f16) : cs
simp' (((m1, WeakTermFloat16 l1), (_, WeakTermFloat t2 l2)):cs)
  | show l1 == show l2 = do
    f16 <- lookupConstantPlus m1 "f16"
    simp $ (f16, t2) : cs
simp' (((_, WeakTermFloat t1 l1), (m2, WeakTermFloat32 l2)):cs)
  | show l1 == show l2 = do
    f32 <- lookupConstantPlus m2 "f32"
    simp $ (t1, f32) : cs
simp' (((m1, WeakTermFloat32 l1), (_, WeakTermFloat t2 l2)):cs)
  | show l1 == show l2 = do
    f32 <- lookupConstantPlus m1 "f32"
    simp $ (f32, t2) : cs
simp' (((_, WeakTermFloat t1 l1), (m2, WeakTermFloat64 l2)):cs)
  | l1 == l2 = do
    f64 <- lookupConstantPlus m2 "f64"
    simp $ (t1, f64) : cs
simp' (((m1, WeakTermFloat64 l1), (_, WeakTermFloat t2 l2)):cs)
  | l1 == l2 = do
    f64 <- lookupConstantPlus m1 "f64"
    simp $ (f64, t2) : cs
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
  tenv <- gets termEnv
  pvenv <- gets patVarEnv
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
        (Just (StuckPiElimUpsilon x1 ess1), Just (StuckPiElimUpsilon x2 ess2))
          | x1 == x2
          , Just pairList <- asPairList ess1 ess2 -> simp $ pairList ++ cs
        (Just (StuckPiElimUpsilon x1@(I (_, i1)) []), _)
          | i1 `S.member` pvenv
          , occurCheck x1 (varWeakTermPlus e2) -> do
            let m = supMeta (metaOf e1) (metaOf e2)
            let e2' = (m, snd e2)
            modify
              (\env -> env {substEnv = IntMap.insert i1 e2' (substEnv env)})
            simp cs
        (_, Just (StuckPiElimUpsilon x2@(I (_, i2)) []))
          | i2 `S.member` pvenv
          , occurCheck x2 (varWeakTermPlus e1) -> do
            let m = supMeta (metaOf e1) (metaOf e2)
            let e1' = (m, snd e1)
            modify
              (\env -> env {substEnv = IntMap.insert i2 e1' (substEnv env)})
            simp cs
        (Just (StuckPiElimConst x1 up1 mess1), _)
          | Just body <- IntMap.lookup (asInt x1) tenv -> do
            body' <- univInstWith up1 $ weaken body
            simp $ (toPiElim body' mess1, e2) : cs
        (_, Just (StuckPiElimConst x2 up2 mess2))
          | Just body <- IntMap.lookup (asInt x2) tenv -> do
            body' <- univInstWith up2 $ weaken body
            simp $ (e1, toPiElim body' mess2) : cs
        (Just (StuckPiElimConst f1 up1 mess1), Just (StuckPiElimConst f2 up2 mess2))
          | f1 == f2
          , Just pairList <- asPairList (map snd mess1) (map snd mess2) -> do
            simpUnivParams up1 up2
            simp $ pairList ++ cs
        (Just (StuckPiElimIter iter1@(_, x1, _, _, _) mess1), Just (StuckPiElimIter (_, x2, _, _, _) mess2))
          | x1 == x2
          , Just _ <- asPairList (map snd mess1) (map snd mess2) -> do
            let c = Enriched (e1, e2) [] $ ConstraintDelta iter1 mess1 mess2
            insConstraintQueue c
            simp cs
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

simpBinder :: [IdentifierPlus] -> [IdentifierPlus] -> WithEnv ()
simpBinder ((m1, x1, t1):xts1) ((m2, x2, t2):xts2) = do
  let var1 = (supMeta m1 m2, WeakTermUpsilon x1)
  let xts2' = substWeakTermPlus' [(x2, var1)] xts2
  simp [(t1, t2)]
  simpBinder xts1 xts2'
simpBinder _ _ = return ()

simpPattern ::
     Identifier
  -> [[WeakTermPlus]]
  -> WeakTermPlus
  -> WeakTermPlus
  -> [PreConstraint]
  -> WithEnv ()
simpPattern h1@(I (_, i)) ies1 _ e2 cs = do
  xss <- mapM toVarList ies1
  let lam = bindFormalArgs e2 xss
  modify (\env -> env {substEnv = IntMap.insert i lam (substEnv env)})
  visit h1
  simp cs

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

simpOther ::
     WeakTermPlus -> WeakTermPlus -> [Hole] -> [PreConstraint] -> WithEnv ()
simpOther e1 e2 fmvs cs = do
  insConstraintQueue $ Enriched (e1, e2) fmvs $ ConstraintOther
  simp cs

simpUnivParams :: UnivParams -> UnivParams -> WithEnv ()
simpUnivParams up1 up2 = do
  let is = IntMap.keys up1
  simpUnivParams' is up1 up2

simpUnivParams' :: [Int] -> UnivParams -> UnivParams -> WithEnv ()
simpUnivParams' [] _ _ = return ()
simpUnivParams' (i:is) up1 up2 = do
  case (IntMap.lookup i up1, IntMap.lookup i up2) of
    (Just l1, Just l2) -> do
      modify (\env -> env {equalityEnv = (l1, l2) : equalityEnv env})
      simpUnivParams' is up1 up2
    _ -> simpUnivParams' is up1 up2

asIdentPlus :: Meta -> WeakTermPlus -> WithEnv IdentifierPlus
asIdentPlus m t = do
  h <- newNameWith' "hole"
  return (m, h, t)

asPairList ::
     [[WeakTermPlus]]
  -> [[WeakTermPlus]]
  -> Maybe [(WeakTermPlus, WeakTermPlus)]
asPairList [] [] = Just []
asPairList (es1:mess1) (es2:mess2)
  | length es1 /= length es2 = Nothing
  | otherwise = do
    pairList <- asPairList mess1 mess2
    return $ zip es1 es2 ++ pairList
asPairList _ _ = Nothing

data Stuck
  = StuckPiElimUpsilon Identifier [[WeakTermPlus]]
  | StuckPiElimZeta Identifier [[WeakTermPlus]]
  | StuckPiElimZetaStrict Identifier [[WeakTermPlus]]
  | StuckPiElimIter IterInfo [(Meta, [WeakTermPlus])]
  | StuckPiElimConst Identifier UnivParams [(Meta, [WeakTermPlus])]

asStuckedTerm :: WeakTermPlus -> Maybe Stuck
asStuckedTerm (_, WeakTermUpsilon x) = Just $ StuckPiElimUpsilon x []
asStuckedTerm (_, WeakTermZeta h) = Just $ StuckPiElimZetaStrict h []
asStuckedTerm (_, WeakTermConst x up) = Just $ StuckPiElimConst x up []
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
      Just (StuckPiElimConst x up ess) ->
        Just $ StuckPiElimConst x up $ ess ++ [(m, es)]
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
    Just (StuckPiElimConst x up ess) ->
      Just $ StuckPiElimConst x up $ ess ++ [(m, es)]
    Just (StuckPiElimUpsilon x ess) -> Just $ StuckPiElimUpsilon x $ ess ++ [es]
    Nothing -> Nothing
asStuckedTerm _ = Nothing

stuckReasonOf :: Stuck -> Maybe Hole
stuckReasonOf (StuckPiElimUpsilon _ _) = Nothing
stuckReasonOf (StuckPiElimZeta h _) = Just h
stuckReasonOf (StuckPiElimZetaStrict h _) = Just h
stuckReasonOf (StuckPiElimIter {}) = Nothing
stuckReasonOf (StuckPiElimConst _ _ _) = Nothing

occurCheck :: Identifier -> [Identifier] -> Bool
occurCheck h fmvs = h `notElem` fmvs

includeCheck :: [Identifier] -> WeakTermPlus -> [Identifier]
includeCheck xs e = filter (`notElem` xs) $ varWeakTermPlus e

getVarList :: [WeakTermPlus] -> [Identifier]
getVarList xs = catMaybes $ map asUpsilon xs

toPiElim :: WeakTermPlus -> [(Meta, [WeakTermPlus])] -> WeakTermPlus
toPiElim e [] = e
toPiElim e ((m, es):ess) = toPiElim (m, WeakTermPiElim e es) ess

unfoldIter :: IterInfo -> WeakTermPlus
unfoldIter (mi, x, xts, body, self) = do
  let m = supMeta mi (metaOf body)
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
toVarList :: [WeakTermPlus] -> WithEnv [IdentifierPlus]
toVarList [] = return []
toVarList ((m, WeakTermUpsilon x):es) = do
  xts <- toVarList es
  let t = (m, WeakTermUpsilon (I ("_", 0)))
  return $ (m, x, t) : xts
toVarList ((m, _):es) = do
  xts <- toVarList es
  x <- newNameWith' "hole"
  let t = (m, WeakTermUpsilon (I ("_", 0)))
  return $ (m, x, t) : xts

bindFormalArgs :: WeakTermPlus -> [[IdentifierPlus]] -> WeakTermPlus
bindFormalArgs e [] = e
bindFormalArgs e (xts:xtss) = do
  let e' = bindFormalArgs e xtss
  (metaOf e', WeakTermPiIntro xts e')

lookupAny :: [Hole] -> IntMap.IntMap a -> Maybe (Hole, a)
lookupAny [] _ = Nothing
lookupAny (h@(I (_, i)):ks) sub = do
  case IntMap.lookup i sub of
    Just v -> Just (h, v)
    _ -> lookupAny ks sub

lookupAll :: [Identifier] -> IntMap.IntMap a -> Maybe [a]
lookupAll [] _ = return []
lookupAll ((I (_, i)):xs) sub = do
  v <- IntMap.lookup i sub
  vs <- lookupAll xs sub
  return $ v : vs

toIntS :: Meta -> IntSize -> WeakTermPlus
toIntS m size = (m, WeakTermEnum $ EnumTypeIntS size)

toIntU :: Meta -> IntSize -> WeakTermPlus
toIntU m size = (m, WeakTermEnum $ EnumTypeIntU size)
