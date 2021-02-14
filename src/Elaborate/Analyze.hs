module Elaborate.Analyze
  ( analyze,
    simp,
    toVarList,
    bindFormalArgs,
    lookupAny,
  )
where

import Control.Monad.State.Lazy
import Data.Constraint
import Data.Env
import Data.Hint
import Data.Ident
import qualified Data.IntMap as IntMap
import Data.Maybe
import qualified Data.PQueue.Min as Q
import qualified Data.Set as S
import qualified Data.Text as T
import Data.WeakTerm
import Elaborate.Infer
import Reduce.WeakTerm

analyze :: WithEnv ()
analyze =
  gets constraintEnv >>= simp

simp :: [PreConstraint] -> WithEnv ()
simp cs =
  case cs of
    [] ->
      return ()
    ((e1, e2) : rest) ->
      simp' $ (reduceWeakTermPlus e1, reduceWeakTermPlus e2) : rest

simp' :: [PreConstraint] -> WithEnv ()
simp' constraintList =
  case constraintList of
    [] ->
      return ()
    (c : cs) ->
      case c of
        ((_, e1), (_, e2))
          | e1 == e2 ->
            simp cs
        (e1@(m1, WeakTermPi xts1 cod1), e2@(m2, WeakTermPi xts2 cod2)) ->
          if length xts1 /= length xts2
            then insConstraintQueue $ Enriched (e1, e2) S.empty ConstraintOther
            else do
              xt1 <- asWeakIdentPlus m1 cod1
              xt2 <- asWeakIdentPlus m2 cod2
              simpBinder (xts1 ++ [xt1]) (xts2 ++ [xt2])
              simp cs
        ((m1, WeakTermPiIntro xts1 e1), (m2, WeakTermPiIntro xts2 e2))
          | length xts1 == length xts2 -> do
            xt1 <- asWeakIdentPlus m1 e1
            xt2 <- asWeakIdentPlus m2 e2
            simpBinder (xts1 ++ [xt1]) (xts2 ++ [xt2])
            simp cs
        ((m1, WeakTermFix xt1@(_, x1, _) xts1 e1), (m2, WeakTermFix xt2@(_, x2, _) xts2 e2))
          | x1 == x2,
            length xts1 == length xts2 -> do
            yt1 <- asWeakIdentPlus m1 e1
            yt2 <- asWeakIdentPlus m2 e2
            simpBinder (xt1 : xts1 ++ [yt1]) (xt2 : xts2 ++ [yt2])
            simp cs
        ((_, WeakTermInt t1 l1), (_, WeakTermInt t2 l2))
          | l1 == l2 ->
            simp $ (t1, t2) : cs
        ((_, WeakTermFloat t1 l1), (_, WeakTermFloat t2 l2))
          | l1 == l2 ->
            simp $ (t1, t2) : cs
        ((_, WeakTermArray dom1 k1), (_, WeakTermArray dom2 k2))
          | k1 == k2 ->
            simp $ (dom1, dom2) : cs
        ((_, WeakTermArrayIntro k1 es1), (_, WeakTermArrayIntro k2 es2))
          | k1 == k2,
            length es1 == length es2 ->
            simp $ zip es1 es2 ++ cs
        ((_, WeakTermStructIntro eks1), (_, WeakTermStructIntro eks2))
          | (es1, ks1) <- unzip eks1,
            (es2, ks2) <- unzip eks2,
            ks1 == ks2 ->
            simp $ zip es1 es2 ++ cs
        ((_, WeakTermQuestion e1 t1), (_, WeakTermQuestion e2 t2)) ->
          simp $ (e1, e2) : (t1, t2) : cs
        (e1@(m1, _), e2@(m2, _)) -> do
          let ms1 = asStuckedTerm e1
          let ms2 = asStuckedTerm e2
          sub <- gets substEnv
          let m = supHint m1 m2
          let zs1 = asterWeakTermPlus e1
          let zs2 = asterWeakTermPlus e2
          -- list of stuck reasons (fmvs: free meta-variables)
          let fmvs = S.union zs1 zs2
          oenv <- gets opaqueEnv
          let fvs1 = S.difference (varWeakTermPlus e1) oenv
          let fvs2 = S.difference (varWeakTermPlus e2) oenv
          case lookupAny (S.toList fmvs) sub of
            Just (h, e) -> do
              let s = IntMap.singleton h e
              let e1' = substWeakTermPlus s (m, snd e1)
              let e2' = substWeakTermPlus s (m, snd e2)
              simp $ (e1', e2') : cs
            Nothing -> do
              let e1' = (m, snd e1)
              let e2' = (m, snd e2)
              case (ms1, ms2) of
                (Just (StuckPiElimUpsilon x1 _ mess1), Just (StuckPiElimUpsilon x2 _ mess2))
                  | x1 == x2,
                    Nothing <- IntMap.lookup (asInt x1) sub,
                    Just pairList <- asPairList (map snd mess1) (map snd mess2) ->
                    simp $ pairList ++ cs
                (Just (StuckPiElimConst x1 _ mess1), Just (StuckPiElimConst x2 _ mess2))
                  | x1 == x2,
                    Just pairList <- asPairList (map snd mess1) (map snd mess2) ->
                    simp $ pairList ++ cs
                (Just (StuckPiElimAsterStrict h1 ies1), _)
                  | xs1 <- concatMap getVarList ies1,
                    occurCheck h1 zs2,
                    isLinear $ filter (`S.member` fvs2) xs1,
                    zs <- includeCheck xs1 fvs2,
                    Just es <- lookupAll zs sub ->
                    case es of
                      [] ->
                        simpPattern h1 ies1 e1' e2' fvs2 cs
                      _ -> do
                        let s = IntMap.fromList $ zip (map asInt zs) es
                        simp $ (e1', substWeakTermPlus s e2') : cs
                (_, Just (StuckPiElimAsterStrict h2 ies2))
                  | xs2 <- concatMap getVarList ies2,
                    occurCheck h2 zs1,
                    isLinear $ filter (`S.member` fvs1) xs2,
                    zs <- includeCheck xs2 fvs1,
                    Just es <- lookupAll zs sub ->
                    case es of
                      [] ->
                        simpPattern h2 ies2 e2' e1' fvs1 cs
                      _ -> do
                        let s = IntMap.fromList $ zip (map asInt zs) es
                        simp $ (substWeakTermPlus s e1', e2') : cs
                (Just (StuckPiElimUpsilon x1 mx1 mess1), _)
                  | Just (mBody, body) <- IntMap.lookup (asInt x1) sub ->
                    simp $ (toPiElim (supHint mx1 mBody, body) mess1, e2) : cs
                (_, Just (StuckPiElimUpsilon x2 mx2 mess2))
                  | Just (mBody, body) <- IntMap.lookup (asInt x2) sub ->
                    simp $ (e1, toPiElim (supHint mx2 mBody, body) mess2) : cs
                (Just (StuckPiElimAsterStrict h1 ies1), _)
                  | xs1 <- concatMap getVarList ies1,
                    occurCheck h1 zs2,
                    zs <- includeCheck xs1 fvs2,
                    Just es <- lookupAll zs sub ->
                    case es of
                      [] ->
                        simpQuasiPattern h1 ies1 e1' e2' fmvs cs
                      _ -> do
                        let s = IntMap.fromList $ zip (map asInt zs) es
                        simp $ (e1', substWeakTermPlus s e2') : cs
                (_, Just (StuckPiElimAsterStrict h2 ies2))
                  | xs2 <- concatMap getVarList ies2,
                    occurCheck h2 zs1,
                    zs <- includeCheck xs2 fvs1,
                    Just es <- lookupAll zs sub ->
                    case es of
                      [] ->
                        simpQuasiPattern h2 ies2 e2' e1' fmvs cs
                      _ -> do
                        let s = IntMap.fromList $ zip (map asInt zs) es
                        simp $ (substWeakTermPlus s e1', e2') : cs
                (Just (StuckPiElimAster h1 ies1), _)
                  | xs1 <- concatMap getVarList ies1,
                    occurCheck h1 zs2,
                    [] <- includeCheck xs1 fvs2 ->
                    simpFlexRigid h1 ies1 e1' e2' fmvs cs
                (_, Just (StuckPiElimAster h2 ies2))
                  | xs2 <- concatMap getVarList ies2,
                    occurCheck h2 zs1,
                    [] <- includeCheck xs2 fvs1 ->
                    simpFlexRigid h2 ies2 e2' e1' fmvs cs
                _ -> do
                  insConstraintQueue $ Enriched (e1, e2) fmvs ConstraintOther
                  simp cs

simpBinder :: [WeakIdentPlus] -> [WeakIdentPlus] -> WithEnv ()
simpBinder =
  simpBinder' IntMap.empty

simpBinder' :: SubstWeakTerm -> [WeakIdentPlus] -> [WeakIdentPlus] -> WithEnv ()
simpBinder' sub args1 args2 =
  case (args1, args2) of
    ((m1, x1, t1) : xts1, (m2, x2, t2) : xts2) -> do
      simp [(t1, substWeakTermPlus sub t2)]
      let var1 = (supHint m1 m2, WeakTermUpsilon x1)
      let sub' = IntMap.insert (asInt x2) var1 sub
      simpBinder' sub' xts1 xts2
    _ ->
      return ()

simpPattern ::
  Int ->
  [[WeakTermPlus]] ->
  WeakTermPlus ->
  WeakTermPlus ->
  S.Set Ident ->
  [PreConstraint] ->
  WithEnv ()
simpPattern i ies1 _ e2 fvs2 cs = do
  xss <- mapM (toVarList fvs2) ies1
  let lam = bindFormalArgs e2 xss
  -- p $ "resolve: " <> T.unpack (asText' h1) <> " ~> " <> T.unpack (toText lam)
  modify (\env -> env {substEnv = IntMap.insert i lam (substEnv env)})
  visit i
  simp cs

simpQuasiPattern ::
  Int ->
  [[WeakTermPlus]] ->
  WeakTermPlus ->
  WeakTermPlus ->
  S.Set Int ->
  [PreConstraint] ->
  WithEnv ()
simpQuasiPattern h1 ies1 e1 e2 fmvs cs = do
  insConstraintQueue $ Enriched (e1, e2) fmvs (ConstraintQuasiPattern h1 ies1 e2)
  simp cs

simpFlexRigid ::
  Int ->
  [[WeakTermPlus]] ->
  WeakTermPlus ->
  WeakTermPlus ->
  S.Set Int ->
  [PreConstraint] ->
  WithEnv ()
simpFlexRigid h1 ies1 e1 e2 fmvs cs = do
  insConstraintQueue $ Enriched (e1, e2) fmvs (ConstraintFlexRigid h1 ies1 e2)
  simp cs

asWeakIdentPlus :: Hint -> WeakTermPlus -> WithEnv WeakIdentPlus
asWeakIdentPlus m t = do
  h <- newNameWith' "aster"
  return (m, h, t)

asPairList ::
  [[WeakTermPlus]] ->
  [[WeakTermPlus]] ->
  Maybe [(WeakTermPlus, WeakTermPlus)]
asPairList list1 list2 =
  case (list1, list2) of
    ([], []) ->
      Just []
    (es1 : mess1, es2 : mess2)
      | length es1 /= length es2 ->
        Nothing
      | otherwise -> do
        pairList <- asPairList mess1 mess2
        return $ zip es1 es2 ++ pairList
    _ ->
      Nothing

data Stuck
  = StuckPiElimUpsilon Ident Hint [(Hint, [WeakTermPlus])]
  | StuckPiElimAster Int [[WeakTermPlus]]
  | StuckPiElimAsterStrict Int [[WeakTermPlus]]
  | StuckPiElimFix FixInfo [(Hint, [WeakTermPlus])]
  | StuckPiElimConst T.Text Hint [(Hint, [WeakTermPlus])]

asStuckedTerm :: WeakTermPlus -> Maybe Stuck
asStuckedTerm term =
  case term of
    (m, WeakTermUpsilon x) ->
      Just $ StuckPiElimUpsilon x m []
    (_, WeakTermAster h) ->
      Just $ StuckPiElimAsterStrict h []
    (m, WeakTermConst x) ->
      Just $ StuckPiElimConst x m []
    (mi, WeakTermFix (_, x, _) xts body) ->
      Just $ StuckPiElimFix (mi, x, xts, body, term) []
    (m, WeakTermPiElim e es) ->
      case asStuckedTerm e of
        Just (StuckPiElimAster h iess) ->
          Just $ StuckPiElimAster h (iess ++ [es])
        Just (StuckPiElimAsterStrict h iexss) ->
          case mapM asUpsilon es of
            Just _ ->
              Just $ StuckPiElimAsterStrict h $ iexss ++ [es]
            Nothing ->
              Just $ StuckPiElimAster h $ iexss ++ [es]
        Just (StuckPiElimFix mu ess) ->
          Just $ StuckPiElimFix mu $ ess ++ [(m, es)]
        Just (StuckPiElimConst x mx ess) ->
          Just $ StuckPiElimConst x mx $ ess ++ [(m, es)]
        Just (StuckPiElimUpsilon x mx ess) ->
          Just $ StuckPiElimUpsilon x mx $ ess ++ [(m, es)]
        Nothing ->
          Nothing
    _ ->
      Nothing

occurCheck :: Int -> S.Set Int -> Bool
occurCheck h fmvs =
  h `S.notMember` fmvs

includeCheck :: [Ident] -> S.Set Ident -> [Ident]
includeCheck xs ys =
  filter (`notElem` xs) $ S.toList ys

getVarList :: [WeakTermPlus] -> [Ident]
getVarList xs =
  catMaybes $ map asUpsilon xs

toPiElim :: WeakTermPlus -> [(Hint, [WeakTermPlus])] -> WeakTermPlus
toPiElim e args =
  case args of
    [] ->
      e
    (m, es) : ess ->
      toPiElim (m, WeakTermPiElim e es) ess

insConstraintQueue :: EnrichedConstraint -> WithEnv ()
insConstraintQueue c =
  modify (\env -> env {constraintQueue = Q.insert c (constraintQueue env)})

visit :: Int -> WithEnv ()
visit h = do
  q <- gets constraintQueue
  let (q1, q2) = Q.partition (\(Enriched _ hs _) -> h `S.member` hs) q
  modify (\env -> env {constraintQueue = q2})
  simp $ map (\(Enriched c _ _) -> c) $ Q.toList q1

toVarList :: S.Set Ident -> [WeakTermPlus] -> WithEnv [WeakIdentPlus]
toVarList =
  toVarList' []

toVarList' :: Context -> S.Set Ident -> [WeakTermPlus] -> WithEnv [WeakIdentPlus]
toVarList' ctx xs termList =
  case termList of
    [] ->
      return []
    e : es
      | (m, WeakTermUpsilon x) <- e,
        x `S.member` xs -> do
        t <- newTypeAsterInCtx ctx m
        xts <- toVarList' (ctx ++ [(m, x, t)]) xs es
        return $ (m, x, t) : xts
      | otherwise -> do
        let m = metaOf e
        t <- newTypeAsterInCtx ctx m
        x <- newNameWith' "aster"
        xts <- toVarList' (ctx ++ [(m, x, t)]) xs es
        return $ (m, x, t) : xts

bindFormalArgs :: WeakTermPlus -> [[WeakIdentPlus]] -> WeakTermPlus
bindFormalArgs e args =
  case args of
    [] ->
      e
    xts : xtss -> do
      let e' = bindFormalArgs e xtss
      (metaOf e', WeakTermPiIntro xts e')

lookupAny :: [Int] -> IntMap.IntMap a -> Maybe (Int, a)
lookupAny is sub =
  case is of
    [] ->
      Nothing
    j : js ->
      case IntMap.lookup j sub of
        Just v ->
          Just (j, v)
        _ ->
          lookupAny js sub

lookupAll :: [Ident] -> IntMap.IntMap a -> Maybe [a]
lookupAll is sub =
  case is of
    [] ->
      return []
    j : js -> do
      v <- IntMap.lookup (asInt j) sub
      vs <- lookupAll js sub
      return $ v : vs
