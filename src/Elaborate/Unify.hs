module Elaborate.Unify
  ( unify,
  )
where

import Control.Exception.Safe
import Control.Monad.State.Lazy
import Data.Basic
import Data.Env
import qualified Data.IntMap as IntMap
import Data.List (partition, sortOn)
import Data.Log
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Text as T
import Data.WeakTerm
import Elaborate.Infer
import Reduce.WeakTerm

data Stuck
  = StuckPiElimUpsilon Ident Hint [(Hint, [WeakTermPlus])]
  | StuckPiElimAster Int [[WeakTermPlus]]

unify :: WithEnv ()
unify =
  analyze >> synthesize

analyze :: WithEnv ()
analyze = do
  cs <- gets constraintEnv
  modify (\env -> env {constraintEnv = []})
  simp cs

synthesize :: WithEnv ()
synthesize = do
  cs <- gets suspendedConstraintEnv
  sub <- gets substEnv
  case cs of
    [] ->
      return ()
    (hs, (e1, e2)) : rest
      | Just (h, e) <- lookupAny (S.toList hs) sub -> do
        modify (\env -> env {suspendedConstraintEnv = rest})
        let s = IntMap.singleton h e
        e1' <- substWeakTermPlus s e1
        e2' <- substWeakTermPlus s e2
        simp [(e1', e2')]
        synthesize
      | otherwise ->
        throwTypeErrors

simp :: [PreConstraint] -> WithEnv ()
simp cs =
  case cs of
    [] ->
      return ()
    ((e1, e2) : rest) -> do
      e1' <- reduceWeakTermPlus e1
      e2' <- reduceWeakTermPlus e2
      b <- isEq e1' e2'
      if b
        then simp rest
        else simp' $ (e1', e2') : rest

simp' :: [PreConstraint] -> WithEnv ()
simp' constraintList =
  case constraintList of
    [] ->
      return ()
    c : cs ->
      case c of
        ((m1, WeakTermPi xts1 cod1), (m2, WeakTermPi xts2 cod2))
          | length xts1 == length xts2 -> do
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
        ((_, WeakTermTensor ts1), (_, WeakTermTensor ts2))
          | length ts1 == length ts2 ->
            simp $ zip ts1 ts2 ++ cs
        ((_, WeakTermTensorIntro es1), (_, WeakTermTensorIntro es2))
          | length es1 == length es2 ->
            simp $ zip es1 es2 ++ cs
        ((_, WeakTermQuestion e1 t1), (_, WeakTermQuestion e2 t2)) ->
          simp $ (e1, e2) : (t1, t2) : cs
        ((_, WeakTermDerangement i1 t1 ekts1), (_, WeakTermDerangement i2 t2 ekts2))
          | length ekts1 == length ekts2,
            i1 == i2,
            (es1, ks1, ts1) <- unzip3 ekts1,
            (es2, ks2, ts2) <- unzip3 ekts2,
            ks1 == ks2 -> do
            simp $ (t1, t2) : zip es1 es2 ++ zip ts1 ts2 ++ cs
        (e1@(m1, _), e2@(m2, _)) -> do
          sub <- gets substEnv
          let m = supHint m1 m2
          let fvs1 = varWeakTermPlus e1
          let fvs2 = varWeakTermPlus e2
          let fmvs1 = asterWeakTermPlus e1
          let fmvs2 = asterWeakTermPlus e2
          let fmvs = S.union fmvs1 fmvs2 -- fmvs: free meta-variables
          case lookupAny (S.toList fmvs) sub of
            Just (h, e) -> do
              let s = IntMap.singleton h e
              e1' <- substWeakTermPlus s (m, snd e1)
              e2' <- substWeakTermPlus s (m, snd e2)
              simp $ (e1', e2') : cs
            Nothing -> do
              let e1' = (m, snd e1)
              let e2' = (m, snd e2)
              case (asStuckedTerm e1, asStuckedTerm e2) of
                (Just (StuckPiElimAster h1 ies1), _)
                  | xs1 <- concatMap getVarList ies1,
                    occurCheck h1 fmvs2,
                    isLinear $ filter (`S.member` fvs2) xs1,
                    zs <- includeCheck xs1 fvs2,
                    Just es <- lookupAll zs sub ->
                    case es of
                      [] -> do
                        xss <- mapM (toVarList fvs2) ies1
                        let lam = bindFormalArgs e2' xss
                        modify (\env -> env {substEnv = IntMap.insert h1 lam (substEnv env)})
                        sus <- gets suspendedConstraintEnv
                        let (sus1, sus2) = partition (\(hs, _) -> S.member h1 hs) sus
                        modify (\env -> env {suspendedConstraintEnv = sus2})
                        simp $ map snd sus1 ++ cs
                      _ -> do
                        let s = IntMap.fromList $ zip (map asInt zs) es
                        e2'' <- substWeakTermPlus s e2'
                        simp $ (e1', e2'') : cs
                (_, Just (StuckPiElimAster h2 ies2))
                  | xs2 <- concatMap getVarList ies2,
                    occurCheck h2 fmvs1,
                    isLinear $ filter (`S.member` fvs1) xs2,
                    zs <- includeCheck xs2 fvs1,
                    Just _ <- lookupAll zs sub ->
                    simp' $ (e2', e1') : cs
                (Just (StuckPiElimUpsilon x1 _ mess1), Just (StuckPiElimUpsilon x2 _ mess2))
                  | x1 == x2,
                    Nothing <- IntMap.lookup (asInt x1) sub,
                    Just pairList <- asPairList (map snd mess1) (map snd mess2) ->
                    simp $ pairList ++ cs
                (Just (StuckPiElimUpsilon x1 mx1 mess1), _)
                  | Just (mBody, body) <- IntMap.lookup (asInt x1) sub ->
                    simp $ (toPiElim (supHint mx1 mBody, body) mess1, e2) : cs
                (_, Just (StuckPiElimUpsilon x2 _ _))
                  | Just _ <- IntMap.lookup (asInt x2) sub ->
                    simp' $ (e2', e1') : cs
                _ -> do
                  modify (\env -> env {suspendedConstraintEnv = (fmvs, (e1, e2)) : suspendedConstraintEnv env})
                  simp cs

simpBinder :: [WeakIdentPlus] -> [WeakIdentPlus] -> WithEnv ()
simpBinder =
  simpBinder' IntMap.empty

simpBinder' :: SubstWeakTerm -> [WeakIdentPlus] -> [WeakIdentPlus] -> WithEnv ()
simpBinder' sub args1 args2 =
  case (args1, args2) of
    ((m1, x1, t1) : xts1, (m2, x2, t2) : xts2) -> do
      t2' <- substWeakTermPlus sub t2
      simp [(t1, t2')]
      let var1 = (supHint m1 m2, WeakTermUpsilon x1)
      let sub' = IntMap.insert (asInt x2) var1 sub
      simpBinder' sub' xts1 xts2
    _ ->
      return ()

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

asStuckedTerm :: WeakTermPlus -> Maybe Stuck
asStuckedTerm term =
  case term of
    (m, WeakTermUpsilon x) ->
      Just $ StuckPiElimUpsilon x m []
    (_, WeakTermAster h) ->
      Just $ StuckPiElimAster h []
    (m, WeakTermPiElim e es) ->
      case asStuckedTerm e of
        Just (StuckPiElimAster h iexss)
          | Just _ <- mapM asUpsilon es ->
            Just $ StuckPiElimAster h $ iexss ++ [es]
        Just (StuckPiElimUpsilon x mx ess) ->
          Just $ StuckPiElimUpsilon x mx $ ess ++ [(m, es)]
        _ ->
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

-- term equality up to alpha-equivalence
isEq :: WeakTermPlus -> WeakTermPlus -> WithEnv Bool
isEq l r =
  case (l, r) of
    ((_, WeakTermTau), (_, WeakTermTau)) ->
      return True
    ((_, WeakTermUpsilon x1), (_, WeakTermUpsilon x2)) ->
      return $ x1 == x2
    ((_, WeakTermPi xts1 cod1), (_, WeakTermPi xts2 cod2)) -> do
      isEq' xts1 cod1 xts2 cod2
    ((_, WeakTermPiIntro xts1 e1), (_, WeakTermPiIntro xts2 e2)) ->
      isEq' xts1 e1 xts2 e2
    ((_, WeakTermPiElim e1 es1), (_, WeakTermPiElim e2 es2)) -> do
      b1 <- isEq e1 e2
      b2 <- and <$> zipWithM isEq es1 es2
      return $ b1 && b2
    ((_, WeakTermFix self1 xts1 e1), (_, WeakTermFix self2 xts2 e2)) ->
      isEq' (self1 : xts1) e1 (self2 : xts2) e2
    ((_, WeakTermAster h1), (_, WeakTermAster h2)) ->
      return $ h1 == h2
    ((_, WeakTermConst a1), (_, WeakTermConst a2)) ->
      return $ a1 == a2
    ((_, WeakTermInt t1 i1), (_, WeakTermInt t2 i2)) -> do
      b <- isEq t1 t2
      return $ b && i1 == i2
    ((_, WeakTermFloat t1 f1), (_, WeakTermFloat t2 f2)) -> do
      b <- isEq t1 t2
      return $ b && f1 == f2
    ((_, WeakTermEnum a1), (_, WeakTermEnum a2)) ->
      return $ a1 == a2
    ((_, WeakTermEnumIntro a1), (_, WeakTermEnumIntro a2)) ->
      return $ a1 == a2
    ((_, WeakTermEnumElim (e1, t1) caseList1), (_, WeakTermEnumElim (e2, t2) caseList2))
      | length caseList1 == length caseList2 -> do
        b1 <- isEq e1 e2
        b2 <- isEq t1 t2
        let (cs1, es1) = unzip caseList1
        let (cs2, es2) = unzip caseList2
        let b3 = map snd cs1 == map snd cs2
        b4 <- and <$> zipWithM isEq es1 es2
        return $ b1 && b2 && b3 && b4
    ((_, WeakTermTensor ts1), (_, WeakTermTensor ts2))
      | length ts1 == length ts2 ->
        and <$> zipWithM isEq ts1 ts2
    ((_, WeakTermTensorIntro es1), (_, WeakTermTensorIntro es2))
      | length es1 == length es2 ->
        and <$> zipWithM isEq es1 es2
    ((_, WeakTermTensorElim xts1 e11 e12), (_, WeakTermTensorElim xts2 e21 e22)) -> do
      b1 <- isEq e11 e21
      b2 <- isEq' xts1 e12 xts2 e22
      return $ b1 && b2
    ((_, WeakTermQuestion e1 t1), (_, WeakTermQuestion e2 t2)) -> do
      b1 <- isEq e1 e2
      b2 <- isEq t1 t2
      return $ b1 && b2
    ((_, WeakTermDerangement d1 e1 args1), (_, WeakTermDerangement d2 e2 args2))
      | length args1 == length args2 -> do
        let b1 = d1 == d2
        b2 <- isEq e1 e2
        let (es1, ks1, ts1) = unzip3 args1
        let (es2, ks2, ts2) = unzip3 args2
        b3 <- and <$> zipWithM isEq es1 es2
        let b4 = ks1 == ks2
        b5 <- and <$> zipWithM isEq ts1 ts2
        return $ b1 && b2 && b3 && b4 && b5
    _ ->
      return False

isEq' :: [WeakIdentPlus] -> WeakTermPlus -> [WeakIdentPlus] -> WeakTermPlus -> WithEnv Bool
isEq' =
  isEq'' IntMap.empty

isEq'' :: SubstWeakTerm -> [WeakIdentPlus] -> WeakTermPlus -> [WeakIdentPlus] -> WeakTermPlus -> WithEnv Bool
isEq'' sub xts1 cod1 xts2 cod2 =
  case (xts1, xts2) of
    ([], []) -> do
      cod2' <- substWeakTermPlus sub cod2
      isEq cod1 cod2'
    (((m1, x1, t1) : rest1), ((_, x2, t2) : rest2)) -> do
      t2' <- substWeakTermPlus sub t2
      b1 <- isEq t1 t2'
      let sub' = IntMap.insert (asInt x2) (m1, WeakTermUpsilon x1) sub
      b2 <- isEq'' sub' rest1 cod1 rest2 cod2
      return $ b1 && b2
    _ ->
      return False

throwTypeErrors :: WithEnv ()
throwTypeErrors = do
  q <- gets suspendedConstraintEnv
  let pcs = sortOn fst $ setupPosInfo q
  errorList <- constructErrors [] pcs
  throw $ Error errorList

setupPosInfo :: [SuspendedConstraint] -> [(PosInfo, PreConstraint)]
setupPosInfo constraintList =
  case constraintList of
    [] ->
      []
    (_, (e1, e2)) : cs -> do
      let pos1 = getPosInfo $ metaOf e1
      let pos2 = getPosInfo $ metaOf e2
      case snd pos1 `compare` snd pos2 of
        LT ->
          (pos2, (e2, e1)) : setupPosInfo cs
        _ ->
          (pos1, (e1, e2)) : setupPosInfo cs

constructErrors :: [PosInfo] -> [(PosInfo, PreConstraint)] -> WithEnv [Log]
constructErrors ps info =
  case info of
    [] ->
      return []
    (pos, (e1, e2)) : pcs -> do
      let msg = constructErrorMsg e1 e2
      as <- constructErrors (pos : ps) pcs
      return $ logError pos msg : as

constructErrorMsg :: WeakTermPlus -> WeakTermPlus -> T.Text
constructErrorMsg e1 e2 =
  "couldn't verify the definitional equality of the following two terms:\n- "
    <> toText e1
    <> "\n- "
    <> toText e2
