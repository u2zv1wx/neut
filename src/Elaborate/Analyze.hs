{-# LANGUAGE OverloadedStrings #-}

module Elaborate.Analyze
  ( analyze
  , simp
  , toVarList
  , bindFormalArgs
  , lookupAny
  ) where

import Control.Monad.State
import Data.Maybe

import qualified Data.HashMap.Strict as Map
import qualified Data.IntMap.Strict as IntMap
import qualified Data.PQueue.Min as Q
import qualified Data.Set as S
import qualified Data.Text as T

import Data.Basic
import Data.Constraint
import Data.Env
import Data.Term (weaken)
import Data.WeakTerm
import Elaborate.Infer
import Reduce.WeakTerm

analyze :: WithEnv ()
analyze = gets constraintEnv >>= simp

simp :: [PreConstraint] -> WithEnv ()
simp [] = return ()
simp ((e1, e2):cs) = simp' $ (reduceWeakTermPlus e1, reduceWeakTermPlus e2) : cs

simp' :: [PreConstraint] -> WithEnv ()
simp' [] = return ()
simp' (((_, e1), (_, e2)):cs)
  | e1 == e2 = simp cs
simp' (((m1, WeakTermPi name1 xts1 cod1), (m2, WeakTermPi name2 xts2 cod2)):cs)
  | name1 == name2 = do
    if length xts1 /= length xts2
      then do
        let m = supMeta m1 m2
        case snd (getPosInfo m1) `compare` snd (getPosInfo m2) of
          LT -> throwArityError m (length xts2) (length xts1)
          _ -> throwArityError m (length xts1) (length xts2)
      else do
        xt1 <- asIdentPlus m1 cod1
        xt2 <- asIdentPlus m2 cod2
        simpBinder (xts1 ++ [xt1]) (xts2 ++ [xt2])
        simp cs
simp' (((m1, WeakTermPiIntro xts1 e1), (m2, WeakTermPiIntro xts2 e2)):cs)
  | length xts1 == length xts2 = do
    xt1 <- asIdentPlus m1 e1
    xt2 <- asIdentPlus m2 e2
    simpBinder (xts1 ++ [xt1]) (xts2 ++ [xt2])
    simp cs
simp' (((m1, WeakTermPiIntroPlus ind1 (name1, is1, args1) xts1 e1), (m2, WeakTermPiIntroPlus ind2 (name2, is2, args2) xts2 e2)):cs)
  | ind1 == ind2
  , name1 == name2
  , is1 == is2
  , length args1 == length args2 = do
    simpBinder args1 args2
    simp $ ((m1, WeakTermPiIntro xts1 e1), (m2, WeakTermPiIntro xts2 e2)) : cs
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
simp' (((_, WeakTermFloat t1 l1), (_, WeakTermFloat t2 l2)):cs)
  | l1 == l2 = simp $ (t1, t2) : cs
simp' (((_, WeakTermEnum (EnumTypeIntS 1)), (_, WeakTermEnum (EnumTypeLabel "bool"))):cs) =
  simp cs
simp' (((_, WeakTermEnum (EnumTypeLabel "bool")), (_, WeakTermEnum (EnumTypeIntS 1))):cs) =
  simp cs
simp' (((_, WeakTermArray dom1 k1), (_, WeakTermArray dom2 k2)):cs)
  | k1 == k2 = simp $ (dom1, dom2) : cs
simp' (((_, WeakTermArrayIntro k1 es1), (_, WeakTermArrayIntro k2 es2)):cs)
  | k1 == k2
  , length es1 == length es2 = simp $ zip es1 es2 ++ cs
simp' (((_, WeakTermStructIntro eks1), (_, WeakTermStructIntro eks2)):cs)
  | (es1, ks1) <- unzip eks1
  , (es2, ks2) <- unzip eks2
  , ks1 == ks2 = simp $ zip es1 es2 ++ cs
simp' (((_, WeakTermQuestion e1 t1), (_, WeakTermQuestion e2 t2)):cs) =
  simp $ (e1, e2) : (t1, t2) : cs
simp' ((e1@(m1, _), e2@(m2, _)):cs) = do
  let ms1 = asStuckedTerm e1
  let ms2 = asStuckedTerm e2
  -- list of stuck reasons (fmvs: free meta-variables)
  sub <- gets substEnv
  cenv <- gets cacheEnv
  let m = supMeta m1 m2
  let hs1 = holeWeakTermPlus e1
  let hs2 = holeWeakTermPlus e2
  let fmvs = S.union hs1 hs2
  let fvs1 = varWeakTermPlus e1
  let fvs2 = varWeakTermPlus e2
  case lookupAny (S.toList fmvs) sub of
    Just (h, e) -> do
      let s = Map.singleton (Left $ asInt h) e
      let e1' = substWeakTermPlus s (m, snd e1)
      let e2' = substWeakTermPlus s (m, snd e2)
      simp $ (e1', e2') : cs
    Nothing -> do
      let e1' = (m, snd e1)
      let e2' = (m, snd e2)
      case (ms1, ms2) of
        (Just (StuckPiElimUpsilon x1 ess1), Just (StuckPiElimUpsilon x2 ess2))
          | x1 == x2
          , Just pairList <- asPairList ess1 ess2 -> simp $ pairList ++ cs
        (Just (StuckPiElimConst x1 _ mess1), Just (StuckPiElimConst x2 _ mess2))
          | x1 == x2
          , Nothing <- Map.lookup x1 cenv
          , Just pairList <- asPairList (map snd mess1) (map snd mess2) -> do
            simp $ pairList ++ cs
        (Just (StuckPiElimZetaStrict h1 ies1), _)
          | xs1 <- concatMap getVarList ies1
          , occurCheck h1 hs2
          , linearCheck $ filter (`S.member` fvs2) xs1
          , zs <- includeCheck xs1 fvs2
          , Just es <- lookupAll zs sub ->
            case es of
              [] -> simpPattern h1 ies1 e1' e2' fvs2 cs
              _ -> do
                let s = Map.fromList $ zip (map (Left . asInt) zs) es
                simp $ (e1', substWeakTermPlus s e2') : cs
        (_, Just (StuckPiElimZetaStrict h2 ies2))
          | xs2 <- concatMap getVarList ies2
          , occurCheck h2 hs1
          , linearCheck $ filter (`S.member` fvs1) xs2
          , zs <- includeCheck xs2 fvs1
          , Just es <- lookupAll zs sub ->
            case es of
              [] -> simpPattern h2 ies2 e2' e1' fvs1 cs
              _
                -- let s = IntMap.fromList $ zip (map asInt zs) es
               -> do
                let s = Map.fromList $ zip (map (Left . asInt) zs) es
                simp $ (substWeakTermPlus s e1', e2') : cs
        (Just (StuckPiElimConst x1 mx1 mess1), _)
          | Just (Left (mBody, body)) <- Map.lookup x1 cenv -> do
            let body' = weaken (supMeta mx1 mBody, body)
            simp $ (toPiElim body' mess1, e2) : cs
        (_, Just (StuckPiElimConst x2 mx2 mess2))
          | Just (Left (mBody, body)) <- Map.lookup x2 cenv -> do
            let body' = weaken (supMeta mx2 mBody, body)
            simp $ (e1, toPiElim body' mess2) : cs
        (Just (StuckPiElimZetaStrict h1 ies1), _)
          | xs1 <- concatMap getVarList ies1
          , occurCheck h1 hs2
          , zs <- includeCheck xs1 fvs2
          , Just es <- lookupAll zs sub ->
            case es of
              [] -> simpQuasiPattern h1 ies1 e1' e2' fmvs cs
              _ -> do
                let s = Map.fromList $ zip (map (Left . asInt) zs) es
                -- let s = IntMap.fromList $ zip (map asInt zs) es
                simp $ (e1', substWeakTermPlus s e2') : cs
        (_, Just (StuckPiElimZetaStrict h2 ies2))
          | xs2 <- concatMap getVarList ies2
          , occurCheck h2 hs1
          , zs <- includeCheck xs2 fvs1
          , Just es <- lookupAll zs sub ->
            case es of
              [] -> simpQuasiPattern h2 ies2 e2' e1' fmvs cs
              _ -> do
                let s = Map.fromList $ zip (map (Left . asInt) zs) es
                -- let s = IntMap.fromList $ zip (map asInt zs) es
                simp $ (substWeakTermPlus s e1', e2') : cs
        (Just (StuckPiElimZeta h1 ies1), Nothing)
          | xs1 <- concatMap getVarList ies1
          , occurCheck h1 hs2
          , [] <- includeCheck xs1 fvs2 -> simpFlexRigid h1 ies1 e1' e2' fmvs cs
        (Nothing, Just (StuckPiElimZeta h2 ies2))
          | xs2 <- concatMap getVarList ies2
          , occurCheck h2 hs1
          , [] <- includeCheck xs2 fvs1 -> simpFlexRigid h2 ies2 e2' e1' fmvs cs
        _ -> do
          insConstraintQueue $ Enriched (e1, e2) fmvs $ ConstraintOther
          simp cs

simpBinder :: [IdentifierPlus] -> [IdentifierPlus] -> WithEnv ()
simpBinder xts1 xts2 = simpBinder' Map.empty xts1 xts2

simpBinder' ::
     SubstWeakTerm -> [IdentifierPlus] -> [IdentifierPlus] -> WithEnv ()
simpBinder' sub ((m1, x1, t1):xts1) ((m2, x2, t2):xts2) = do
  simp [(t1, substWeakTermPlus sub t2)]
  let var1 = (supMeta m1 m2, WeakTermUpsilon x1)
  let sub' = Map.insert (Left $ asInt x2) var1 sub
  simpBinder' sub' xts1 xts2
simpBinder' _ _ _ = return ()

simpPattern ::
     Identifier
  -> [[WeakTermPlus]]
  -> WeakTermPlus
  -> WeakTermPlus
  -> S.Set Identifier
  -> [PreConstraint]
  -> WithEnv ()
simpPattern h1@(I (_, i)) ies1 _ e2 fvs2 cs = do
  xss <- mapM (toVarList fvs2) ies1
  let lam = bindFormalArgs e2 xss
  -- p $ "resolve: " <> T.unpack (asText' h1) <> " ~> " <> T.unpack (toText lam)
  modify (\env -> env {substEnv = IntMap.insert i lam (substEnv env)})
  visit h1
  simp cs

simpQuasiPattern ::
     Identifier
  -> [[WeakTermPlus]]
  -> WeakTermPlus
  -> WeakTermPlus
  -> S.Set Identifier
  -> [PreConstraint]
  -> WithEnv ()
simpQuasiPattern h1 ies1 e1 e2 fmvs cs = do
  insConstraintQueue $
    Enriched (e1, e2) fmvs (ConstraintQuasiPattern h1 ies1 e2)
  simp cs

simpFlexRigid ::
     Identifier
  -> [[WeakTermPlus]]
  -> WeakTermPlus
  -> WeakTermPlus
  -> S.Set Identifier
  -> [PreConstraint]
  -> WithEnv ()
simpFlexRigid h1 ies1 e1 e2 fmvs cs = do
  insConstraintQueue $ Enriched (e1, e2) fmvs (ConstraintFlexRigid h1 ies1 e2)
  simp cs

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
  | StuckPiElimConst T.Text Meta [(Meta, [WeakTermPlus])]

asStuckedTerm :: WeakTermPlus -> Maybe Stuck
asStuckedTerm (_, WeakTermUpsilon x) = Just $ StuckPiElimUpsilon x []
asStuckedTerm (_, WeakTermZeta h) = Just $ StuckPiElimZetaStrict h []
asStuckedTerm (m, WeakTermConst x) = Just $ StuckPiElimConst x m []
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
      Just (StuckPiElimConst x mx ess) ->
        Just $ StuckPiElimConst x mx $ ess ++ [(m, es)]
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
    Just (StuckPiElimConst x mx ess) ->
      Just $ StuckPiElimConst x mx $ ess ++ [(m, es)]
    Just (StuckPiElimUpsilon x ess) -> Just $ StuckPiElimUpsilon x $ ess ++ [es]
    Nothing -> Nothing
asStuckedTerm _ = Nothing

occurCheck :: Identifier -> S.Set Identifier -> Bool
occurCheck h fmvs = h `S.notMember` fmvs

includeCheck :: [Identifier] -> S.Set Identifier -> [Identifier]
includeCheck xs ys = filter (`notElem` xs) $ S.toList ys

getVarList :: [WeakTermPlus] -> [Identifier]
getVarList xs = catMaybes $ map asUpsilon xs

toPiElim :: WeakTermPlus -> [(Meta, [WeakTermPlus])] -> WeakTermPlus
toPiElim e [] = e
toPiElim e ((m, es):ess) = toPiElim (m, WeakTermPiElim e es) ess

insConstraintQueue :: EnrichedConstraint -> WithEnv ()
insConstraintQueue c =
  modify (\env -> env {constraintQueue = Q.insert c (constraintQueue env)})

visit :: Identifier -> WithEnv ()
visit h = do
  q <- gets constraintQueue
  let (q1, q2) = Q.partition (\(Enriched _ hs _) -> h `S.member` hs) q
  modify (\env -> env {constraintQueue = q2})
  simp $ map (\(Enriched c _ _) -> c) $ Q.toList q1

toVarList :: S.Set Identifier -> [WeakTermPlus] -> WithEnv [IdentifierPlus]
toVarList xs es = toVarList' [] xs es

toVarList' ::
     Context -> S.Set Identifier -> [WeakTermPlus] -> WithEnv [IdentifierPlus]
toVarList' _ _ [] = return []
toVarList' ctx xs (e:es)
  | (m, WeakTermUpsilon x) <- e
  , x `S.member` xs = do
    t <- newTypeHoleInCtx ctx m
    xts <- toVarList' (ctx ++ [(m, x, t)]) xs es
    return $ (m, x, t) : xts
  | otherwise = do
    let m = metaOf e
    t <- newTypeHoleInCtx ctx m
    x <- newNameWith' "hole"
    xts <- toVarList' (ctx ++ [(m, x, t)]) xs es
    return $ (m, x, t) : xts

bindFormalArgs :: WeakTermPlus -> [[IdentifierPlus]] -> WeakTermPlus
bindFormalArgs e [] = e
bindFormalArgs e (xts:xtss) = do
  let e' = bindFormalArgs e xtss
  (metaOf e', WeakTermPiIntro xts e')

lookupAny :: [Identifier] -> IntMap.IntMap a -> Maybe (Identifier, a)
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

throwArityError :: Meta -> Int -> Int -> WithEnv a
throwArityError m i1 i2 =
  raiseError m $
  "the arity of the term is " <>
  T.pack (show i1) <> ", but found " <> T.pack (show i2) <> " arguments"
