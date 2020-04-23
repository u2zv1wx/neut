module Elaborate.Analyze
  ( analyze,
    simp,
    toVarList,
    bindFormalArgs,
    lookupAny,
  )
where

import Control.Monad.State.Lazy
import Data.Basic
import Data.Constraint
import Data.Env
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
        ((m1, WeakTermPi name1 xts1 cod1), (m2, WeakTermPi name2 xts2 cod2))
          | name1 == name2 ->
            if length xts1 /= length xts2
              then do
                let m = supMeta m1 m2
                case snd (getPosInfo m1) `compare` snd (getPosInfo m2) of
                  LT ->
                    throwArityError m (length xts2) (length xts1)
                  _ ->
                    throwArityError m (length xts1) (length xts2)
              else do
                xt1 <- asWeakIdentPlus m1 cod1
                xt2 <- asWeakIdentPlus m2 cod2
                simpBinder (xts1 ++ [xt1]) (xts2 ++ [xt2])
                simp cs
        ((m1, WeakTermPiIntro Nothing xts1 e1), (m2, WeakTermPiIntro Nothing xts2 e2))
          | length xts1 == length xts2 -> do
            xt1 <- asWeakIdentPlus m1 e1
            xt2 <- asWeakIdentPlus m2 e2
            simpBinder (xts1 ++ [xt1]) (xts2 ++ [xt2])
            simp cs
        ((m1, WeakTermPiIntro (Just (indName1, consName1, args1)) xts1 e1), (m2, WeakTermPiIntro (Just (indName2, consName2, args2)) xts2 e2))
          | indName1 == indName2,
            consName1 == consName2,
            length args1 == length args2 -> do
            simpBinder args1 args2
            simp $ ((m1, weakTermPiIntro xts1 e1), (m2, weakTermPiIntro xts2 e2)) : cs
        ((m1, WeakTermIter xt1@(_, x1, _) xts1 e1), (m2, WeakTermIter xt2@(_, x2, _) xts2 e2))
          | x1 == x2,
            length xts1 == length xts2 -> do
            yt1 <- asWeakIdentPlus m1 e1
            yt2 <- asWeakIdentPlus m2 e2
            simpBinder (xt1 : xts1 ++ [yt1]) (xt2 : xts2 ++ [yt2])
            simp cs
        ((_, WeakTermInt t1 l1), (m, WeakTermEnumIntro (EnumValueIntS s2 l2)))
          | l1 == l2 ->
            simp $ (t1, toIntS m s2) : cs
        ((m, WeakTermEnumIntro (EnumValueIntS s1 l1)), (_, WeakTermInt t2 l2))
          | l1 == l2 ->
            simp $ (toIntS m s1, t2) : cs
        ((_, WeakTermInt t1 l1), (m, WeakTermEnumIntro (EnumValueIntU s2 l2)))
          | l1 == l2 ->
            simp $ (t1, toIntU m s2) : cs
        ((m, WeakTermEnumIntro (EnumValueIntU s1 l1)), (_, WeakTermInt t2 l2))
          | l1 == l2 ->
            simp $ (toIntU m s1, t2) : cs
        ((_, WeakTermInt t1 l1), (_, WeakTermInt t2 l2))
          | l1 == l2 ->
            simp $ (t1, t2) : cs
        ((_, WeakTermFloat t1 l1), (_, WeakTermFloat t2 l2))
          | l1 == l2 ->
            simp $ (t1, t2) : cs
        ((_, WeakTermEnum (EnumTypeIntS 1)), (_, WeakTermEnum (EnumTypeLabel "bool"))) ->
          simp cs
        ((_, WeakTermEnum (EnumTypeLabel "bool")), (_, WeakTermEnum (EnumTypeIntS 1))) ->
          simp cs
        ((_, WeakTermArray dom1 k1), (_, WeakTermArray dom2 k2))
          | k1 == k2 -> simp $ (dom1, dom2) : cs
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
          -- simp' ((e1@(m1, _), e2@(m2, _)) : cs) = do
          let ms1 = asStuckedTerm e1
          let ms2 = asStuckedTerm e2
          -- list of stuck reasons (fmvs: free meta-variables)
          sub <- gets substEnv
          let m = supMeta m1 m2
          let hs1 = holeWeakTermPlus e1
          let hs2 = holeWeakTermPlus e2
          let fmvs = S.union hs1 hs2
          let fvs1 = varWeakTermPlus e1
          let fvs2 = varWeakTermPlus e2
          case lookupAny (S.toList fmvs) sub of
            Just (h, e) -> do
              let s = IntMap.singleton (asInt h) e
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
                (Just (StuckPiElimHoleStrict h1 ies1), _)
                  | xs1 <- concatMap getVarList ies1,
                    occurCheck h1 hs2,
                    linearCheck $ filter (`S.member` fvs2) xs1,
                    zs <- includeCheck xs1 fvs2,
                    Just es <- lookupAll zs sub ->
                    case es of
                      [] ->
                        simpPattern h1 ies1 e1' e2' fvs2 cs
                      _ -> do
                        let s = IntMap.fromList $ zip (map asInt zs) es
                        simp $ (e1', substWeakTermPlus s e2') : cs
                (_, Just (StuckPiElimHoleStrict h2 ies2))
                  | xs2 <- concatMap getVarList ies2,
                    occurCheck h2 hs1,
                    linearCheck $ filter (`S.member` fvs1) xs2,
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
                    simp $ (toPiElim (supMeta mx1 mBody, body) mess1, e2) : cs
                (_, Just (StuckPiElimUpsilon x2 mx2 mess2))
                  | Just (mBody, body) <- IntMap.lookup (asInt x2) sub ->
                    simp $ (e1, toPiElim (supMeta mx2 mBody, body) mess2) : cs
                (Just (StuckPiElimHoleStrict h1 ies1), _)
                  | xs1 <- concatMap getVarList ies1,
                    occurCheck h1 hs2,
                    zs <- includeCheck xs1 fvs2,
                    Just es <- lookupAll zs sub ->
                    case es of
                      [] ->
                        simpQuasiPattern h1 ies1 e1' e2' fmvs cs
                      _ -> do
                        let s = IntMap.fromList $ zip (map asInt zs) es
                        simp $ (e1', substWeakTermPlus s e2') : cs
                (_, Just (StuckPiElimHoleStrict h2 ies2))
                  | xs2 <- concatMap getVarList ies2,
                    occurCheck h2 hs1,
                    zs <- includeCheck xs2 fvs1,
                    Just es <- lookupAll zs sub ->
                    case es of
                      [] ->
                        simpQuasiPattern h2 ies2 e2' e1' fmvs cs
                      _ -> do
                        let s = IntMap.fromList $ zip (map asInt zs) es
                        simp $ (substWeakTermPlus s e1', e2') : cs
                (Just (StuckPiElimHole h1 ies1), Nothing)
                  | xs1 <- concatMap getVarList ies1,
                    occurCheck h1 hs2,
                    [] <- includeCheck xs1 fvs2 ->
                    simpFlexRigid h1 ies1 e1' e2' fmvs cs
                (Nothing, Just (StuckPiElimHole h2 ies2))
                  | xs2 <- concatMap getVarList ies2,
                    occurCheck h2 hs1,
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
      let var1 = (supMeta m1 m2, WeakTermUpsilon x1)
      let sub' = IntMap.insert (asInt x2) var1 sub
      simpBinder' sub' xts1 xts2
    _ ->
      return ()

simpPattern ::
  Ident ->
  [[WeakTermPlus]] ->
  WeakTermPlus ->
  WeakTermPlus ->
  S.Set Ident ->
  [PreConstraint] ->
  WithEnv ()
simpPattern h1@(I (_, i)) ies1 _ e2 fvs2 cs = do
  xss <- mapM (toVarList fvs2) ies1
  let lam = bindFormalArgs e2 xss
  -- p $ "resolve: " <> T.unpack (asText' h1) <> " ~> " <> T.unpack (toText lam)
  modify (\env -> env {substEnv = IntMap.insert i lam (substEnv env)})
  visit h1
  simp cs

simpQuasiPattern ::
  Ident ->
  [[WeakTermPlus]] ->
  WeakTermPlus ->
  WeakTermPlus ->
  S.Set Ident ->
  [PreConstraint] ->
  WithEnv ()
simpQuasiPattern h1 ies1 e1 e2 fmvs cs = do
  insConstraintQueue $ Enriched (e1, e2) fmvs (ConstraintQuasiPattern h1 ies1 e2)
  simp cs

simpFlexRigid ::
  Ident ->
  [[WeakTermPlus]] ->
  WeakTermPlus ->
  WeakTermPlus ->
  S.Set Ident ->
  [PreConstraint] ->
  WithEnv ()
simpFlexRigid h1 ies1 e1 e2 fmvs cs = do
  insConstraintQueue $ Enriched (e1, e2) fmvs (ConstraintFlexRigid h1 ies1 e2)
  simp cs

asWeakIdentPlus :: Meta -> WeakTermPlus -> WithEnv WeakIdentPlus
asWeakIdentPlus m t = do
  h <- newNameWith' "hole"
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
  = StuckPiElimUpsilon Ident Meta [(Meta, [WeakTermPlus])]
  | StuckPiElimHole Ident [[WeakTermPlus]]
  | StuckPiElimHoleStrict Ident [[WeakTermPlus]]
  | StuckPiElimIter IterInfo [(Meta, [WeakTermPlus])]
  | StuckPiElimConst T.Text Meta [(Meta, [WeakTermPlus])]

asStuckedTerm :: WeakTermPlus -> Maybe Stuck
asStuckedTerm term =
  case term of
    (m, WeakTermUpsilon x) ->
      Just $ StuckPiElimUpsilon x m []
    (_, WeakTermHole h) ->
      Just $ StuckPiElimHoleStrict h []
    (m, WeakTermConst x) ->
      Just $ StuckPiElimConst x m []
    (mi, WeakTermIter (_, x, _) xts body) ->
      Just $ StuckPiElimIter (mi, x, xts, body, term) []
    (m, WeakTermPiElim e es) ->
      case asStuckedTerm e of
        Just (StuckPiElimHole h iess) ->
          Just $ StuckPiElimHole h (iess ++ [es])
        Just (StuckPiElimHoleStrict h iexss) ->
          case mapM asUpsilon es of
            Just _ ->
              Just $ StuckPiElimHoleStrict h $ iexss ++ [es]
            Nothing ->
              Just $ StuckPiElimHole h $ iexss ++ [es]
        Just (StuckPiElimIter mu ess) ->
          Just $ StuckPiElimIter mu $ ess ++ [(m, es)]
        Just (StuckPiElimConst x mx ess) ->
          Just $ StuckPiElimConst x mx $ ess ++ [(m, es)]
        Just (StuckPiElimUpsilon x mx ess) ->
          Just $ StuckPiElimUpsilon x mx $ ess ++ [(m, es)]
        Nothing ->
          Nothing
    _ ->
      Nothing

occurCheck :: Ident -> S.Set Ident -> Bool
occurCheck h fmvs =
  h `S.notMember` fmvs

includeCheck :: [Ident] -> S.Set Ident -> [Ident]
includeCheck xs ys =
  filter (`notElem` xs) $ S.toList ys

getVarList :: [WeakTermPlus] -> [Ident]
getVarList xs =
  catMaybes $ map asUpsilon xs

toPiElim :: WeakTermPlus -> [(Meta, [WeakTermPlus])] -> WeakTermPlus
toPiElim e args =
  case args of
    [] ->
      e
    (m, es) : ess ->
      toPiElim (m, WeakTermPiElim e es) ess

insConstraintQueue :: EnrichedConstraint -> WithEnv ()
insConstraintQueue c =
  modify (\env -> env {constraintQueue = Q.insert c (constraintQueue env)})

visit :: Ident -> WithEnv ()
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
        t <- newTypeHoleInCtx ctx m
        xts <- toVarList' (ctx ++ [(m, x, t)]) xs es
        return $ (m, x, t) : xts
      | otherwise -> do
        let m = metaOf e
        t <- newTypeHoleInCtx ctx m
        x <- newNameWith' "hole"
        xts <- toVarList' (ctx ++ [(m, x, t)]) xs es
        return $ (m, x, t) : xts

bindFormalArgs :: WeakTermPlus -> [[WeakIdentPlus]] -> WeakTermPlus
bindFormalArgs e args =
  case args of
    [] ->
      e
    xts : xtss -> do
      let e' = bindFormalArgs e xtss
      (metaOf e', weakTermPiIntro xts e')

lookupAny :: [Ident] -> IntMap.IntMap a -> Maybe (Ident, a)
lookupAny is sub =
  case is of
    [] ->
      Nothing
    j : js ->
      case IntMap.lookup (asInt j) sub of
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

toIntS :: Meta -> IntSize -> WeakTermPlus
toIntS m size =
  (m, WeakTermEnum $ EnumTypeIntS size)

toIntU :: Meta -> IntSize -> WeakTermPlus
toIntU m size =
  (m, WeakTermEnum $ EnumTypeIntU size)

throwArityError :: Meta -> Int -> Int -> WithEnv a
throwArityError m i1 i2 =
  raiseError m $
    "the arity of the term is "
      <> T.pack (show i1)
      <> ", but found "
      <> T.pack (show i2)
      <> " arguments"
