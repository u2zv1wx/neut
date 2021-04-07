module Elaborate.Simplify
  ( simplify,
  )
where

import Control.Monad.State.Lazy
import Data.Basic
import Data.Env
import qualified Data.IntMap as IntMap
import Data.Maybe (catMaybes)
import qualified Data.PQueue.Min as Q
import qualified Data.Set as S
import Data.WeakTerm
import Reduce.WeakTerm

data Stuck
  = StuckPiElimVar Ident [(Hint, [WeakTermPlus])]
  | StuckPiElimVarOpaque Ident [(Hint, [WeakTermPlus])]
  | StuckPiElimAster Int [[WeakTermPlus]]
  deriving (Show)

simplify :: [(Constraint, Constraint)] -> WithEnv ()
simplify cs =
  case cs of
    [] ->
      return ()
    ((e1, e2), orig) : rest -> do
      e1' <- reduceWeakTermPlus e1
      e2' <- reduceWeakTermPlus e2
      b <- isEq e1' e2'
      if b
        then simplify rest
        else simplify' $ ((e1', e2'), orig) : rest

simplify' :: [(Constraint, Constraint)] -> WithEnv ()
simplify' constraintList =
  case constraintList of
    [] ->
      return ()
    (c, orig) : cs ->
      case c of
        ((m1, WeakTermPi xts1 cod1), (m2, WeakTermPi xts2 cod2))
          | length xts1 == length xts2 -> do
            xt1 <- asWeakIdentPlus m1 cod1
            xt2 <- asWeakIdentPlus m2 cod2
            simplifyBinder orig (xts1 ++ [xt1]) (xts2 ++ [xt2])
            simplify cs
        ((m1, WeakTermPiIntro _ kind1 xts1 e1), (m2, WeakTermPiIntro _ kind2 xts2 e2))
          | LamKindFix xt1@(_, x1, _) <- kind1,
            LamKindFix xt2@(_, x2, _) <- kind2,
            x1 == x2,
            length xts1 == length xts2 -> do
            yt1 <- asWeakIdentPlus m1 e1
            yt2 <- asWeakIdentPlus m2 e2
            simplifyBinder orig (xt1 : xts1 ++ [yt1]) (xt2 : xts2 ++ [yt2])
            simplify cs
          | lamKindWeakEq kind1 kind2,
            length xts1 == length xts2 -> do
            xt1 <- asWeakIdentPlus m1 e1
            xt2 <- asWeakIdentPlus m2 e2
            simplifyBinder orig (xts1 ++ [xt1]) (xts2 ++ [xt2])
            simplify cs
        ((_, WeakTermInt t1 l1), (_, WeakTermInt t2 l2))
          | l1 == l2 ->
            simplify $ ((t1, t2), orig) : cs
        ((_, WeakTermFloat t1 l1), (_, WeakTermFloat t2 l2))
          | l1 == l2 ->
            simplify $ ((t1, t2), orig) : cs
        ((_, WeakTermTensor ts1), (_, WeakTermTensor ts2))
          | length ts1 == length ts2 ->
            simplify $ map (\item -> (item, orig)) (zip ts1 ts2) ++ cs
        ((_, WeakTermTensorIntro es1), (_, WeakTermTensorIntro es2))
          | length es1 == length es2 ->
            simplify $ map ((,) orig) (zip es1 es2) ++ cs
        ((_, WeakTermQuestion e1 t1), (_, WeakTermQuestion e2 t2)) ->
          simplify $ ((e1, e2), orig) : ((t1, t2), orig) : cs
        ((_, WeakTermDerangement i1 t1 ekts1), (_, WeakTermDerangement i2 t2 ekts2))
          | length ekts1 == length ekts2,
            i1 == i2,
            (es1, ks1, ts1) <- unzip3 ekts1,
            (es2, ks2, ts2) <- unzip3 ekts2,
            ks1 == ks2 -> do
            simplify $ map ((,) orig) ((t1, t2) : zip es1 es2 ++ zip ts1 ts2) ++ cs
        (e1, e2) -> do
          sub <- gets substEnv
          let fvs1 = varWeakTermPlus e1
          let fvs2 = varWeakTermPlus e2
          let fmvs1 = asterWeakTermPlus e1
          let fmvs2 = asterWeakTermPlus e2
          let fmvs = S.union fmvs1 fmvs2 -- fmvs: free meta-variables
          case (lookupAny (S.toList fmvs1) sub, lookupAny (S.toList fmvs2) sub) of
            (Just (h1, body1), Just (h2, body2)) -> do
              let s1 = IntMap.singleton h1 body1
              let s2 = IntMap.singleton h2 body2
              e1' <- substWeakTermPlus s1 e1
              e2' <- substWeakTermPlus s2 e2
              simplify $ ((e1', e2'), orig) : cs
            (Just (h1, body1), Nothing) -> do
              let s1 = IntMap.singleton h1 body1
              e1' <- substWeakTermPlus s1 e1
              simplify $ ((e1', e2), orig) : cs
            (Nothing, Just (h2, body2)) -> do
              let s2 = IntMap.singleton h2 body2
              e2' <- substWeakTermPlus s2 e2
              simplify $ ((e1, e2'), orig) : cs
            (Nothing, Nothing) -> do
              case (asStuckedTerm e1, asStuckedTerm e2) of
                (Just (StuckPiElimAster h1 ies1), _)
                  | Just xss1 <- mapM asIdentList ies1,
                    Just argSet1 <- toLinearIdentSet xss1,
                    h1 `S.notMember` fmvs2,
                    fvs2 `S.isSubsetOf` argSet1 ->
                    resolveHole h1 xss1 e2 cs
                (_, Just (StuckPiElimAster h2 ies2))
                  | Just xss2 <- mapM asIdentList ies2,
                    Just argSet2 <- toLinearIdentSet xss2,
                    h2 `S.notMember` fmvs1,
                    fvs1 `S.isSubsetOf` argSet2 ->
                    resolveHole h2 xss2 e1 cs
                (Just (StuckPiElimVarOpaque x1 mess1), Just (StuckPiElimVarOpaque x2 mess2))
                  | x1 == x2,
                    Just pairList <- asPairList (map snd mess1) (map snd mess2) ->
                    simplify $ map ((,) orig) pairList ++ cs
                (Just (StuckPiElimVar x1 mess1), Just (StuckPiElimVar x2 mess2))
                  | x1 == x2,
                    Just lam <- lookupDefinition x1 sub -> do
                    simplify $ ((toPiElim lam mess1, toPiElim lam mess2), orig) : cs
                (Just (StuckPiElimVar x1 mess1), Just (StuckPiElimVar x2 mess2))
                  | x1 /= x2,
                    Just lam1 <- lookupDefinition x1 sub,
                    Just lam2 <- lookupDefinition x2 sub -> do
                    if asInt x1 > asInt x2
                      then simplify $ ((toPiElim lam1 mess1, e2), orig) : cs
                      else simplify $ ((e1, toPiElim lam2 mess2), orig) : cs
                (Just (StuckPiElimVar x1 mess1), Just (StuckPiElimAster {}))
                  | Just lam <- lookupDefinition x1 sub -> do
                    let susCon = SusCon (fmvs, ((e1, e2), orig), ConDelta (toPiElim lam mess1, e2))
                    modify (\env -> env {suspendedConstraintEnv = Q.insert susCon (suspendedConstraintEnv env)})
                    simplify cs
                (Just (StuckPiElimAster {}), Just (StuckPiElimVar x2 mess2))
                  | Just lam <- lookupDefinition x2 sub -> do
                    let susCon = SusCon (fmvs, ((e1, e2), orig), ConDelta (e1, toPiElim lam mess2))
                    modify (\env -> env {suspendedConstraintEnv = Q.insert susCon (suspendedConstraintEnv env)})
                    simplify cs
                (Just (StuckPiElimVar x1 mess1), _)
                  | Just lam <- lookupDefinition x1 sub -> do
                    simplify $ ((toPiElim lam mess1, e2), orig) : cs
                (_, Just (StuckPiElimVar x2 mess2))
                  | Just lam <- lookupDefinition x2 sub -> do
                    simplify $ ((e1, toPiElim lam mess2), orig) : cs
                _ -> do
                  let susCon = SusCon (fmvs, ((e1, e2), orig), ConOther)
                  modify (\env -> env {suspendedConstraintEnv = Q.insert susCon (suspendedConstraintEnv env)})
                  simplify cs

resolveHole :: Int -> [[WeakIdentPlus]] -> WeakTermPlus -> [(Constraint, Constraint)] -> WithEnv ()
resolveHole h1 xss e2' cs = do
  modify (\env -> env {substEnv = IntMap.insert h1 (toPiIntro xss e2') (substEnv env)})
  -- p $ T.unpack $ "resolve: " <> T.pack (show h1) <> " ~> " <> toText (toPiIntro xss e2')
  sus <- gets suspendedConstraintEnv
  let (sus1, sus2) = Q.partition (\(SusCon (hs, _, _)) -> S.member h1 hs) sus
  modify (\env -> env {suspendedConstraintEnv = sus2})
  let sus1' = map (\(SusCon (_, c, _)) -> c) $ Q.toList sus1
  simplify $ sus1' ++ cs

simplifyBinder :: Constraint -> [WeakIdentPlus] -> [WeakIdentPlus] -> WithEnv ()
simplifyBinder orig =
  simplifyBinder' orig IntMap.empty

simplifyBinder' :: Constraint -> SubstWeakTerm -> [WeakIdentPlus] -> [WeakIdentPlus] -> WithEnv ()
simplifyBinder' orig sub args1 args2 =
  case (args1, args2) of
    ((m1, x1, t1) : xts1, (_, x2, t2) : xts2) -> do
      t2' <- substWeakTermPlus sub t2
      simplify [((t1, t2'), orig)]
      let var1 = (m1, WeakTermVar VarKindLocal x1)
      let sub' = IntMap.insert (asInt x2) var1 sub
      simplifyBinder' orig sub' xts1 xts2
    _ ->
      return ()

asWeakIdentPlus :: Hint -> WeakTermPlus -> WithEnv WeakIdentPlus
asWeakIdentPlus m t = do
  h <- newIdentFromText "aster"
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
    (_, WeakTermVar opacity x) ->
      case opacity of
        VarKindLocal ->
          Just $ StuckPiElimVarOpaque x []
        VarKindGlobalOpaque ->
          Just $ StuckPiElimVarOpaque x []
        VarKindGlobalTransparent ->
          Just $ StuckPiElimVar x []
    (_, WeakTermAster h) ->
      Just $ StuckPiElimAster h []
    (m, WeakTermPiElim e es) ->
      case asStuckedTerm e of
        Just (StuckPiElimAster h iexss)
          | Just _ <- mapM asVar es ->
            Just $ StuckPiElimAster h $ iexss ++ [es]
        Just (StuckPiElimVar x ess) ->
          Just $ StuckPiElimVar x $ ess ++ [(m, es)]
        Just (StuckPiElimVarOpaque x ess) ->
          Just $ StuckPiElimVarOpaque x $ ess ++ [(m, es)]
        _ ->
          Nothing
    _ ->
      Nothing

toPiIntro :: [[WeakIdentPlus]] -> WeakTermPlus -> WeakTermPlus
toPiIntro args e =
  case args of
    [] ->
      e
    xts : xtss -> do
      let e' = toPiIntro xtss e
      (metaOf e', WeakTermPiIntro OpacityTransparent LamKindNormal xts e')

toPiElim :: WeakTermPlus -> [(Hint, [WeakTermPlus])] -> WeakTermPlus
toPiElim e args =
  case args of
    [] ->
      e
    (m, es) : ess ->
      toPiElim (m, WeakTermPiElim e es) ess

asIdentList :: [WeakTermPlus] -> Maybe [WeakIdentPlus]
asIdentList termList =
  case termList of
    [] ->
      return []
    e : es
      | (m, WeakTermVar _ x) <- e -> do
        let t = (m, WeakTermTau) -- don't care
        xts <- asIdentList es
        return $ (m, x, t) : xts
      | otherwise ->
        Nothing

{-# INLINE toLinearIdentSet #-}
toLinearIdentSet :: [[WeakIdentPlus]] -> Maybe (S.Set Ident)
toLinearIdentSet xtss =
  toLinearIdentSet' xtss S.empty

toLinearIdentSet' :: [[WeakIdentPlus]] -> S.Set Ident -> Maybe (S.Set Ident)
toLinearIdentSet' xtss acc =
  case xtss of
    [] ->
      return acc
    [] : rest ->
      toLinearIdentSet' rest acc
    ((_, x, _) : rest1) : rest2
      | x `S.member` acc ->
        Nothing
      | otherwise ->
        toLinearIdentSet' (rest1 : rest2) (S.insert x acc)

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

{-# INLINE lookupDefinition #-}
lookupDefinition :: Ident -> (IntMap.IntMap WeakTermPlus) -> Maybe WeakTermPlus
lookupDefinition x sub =
  IntMap.lookup (asInt x) sub

-- term equality up to alpha-equivalence
isEq :: WeakTermPlus -> WeakTermPlus -> WithEnv Bool
isEq l r =
  case (l, r) of
    ((_, WeakTermTau), (_, WeakTermTau)) ->
      return True
    ((_, WeakTermVar _ x1), (_, WeakTermVar _ x2)) ->
      return $ x1 == x2
    ((_, WeakTermPi xts1 cod1), (_, WeakTermPi xts2 cod2)) -> do
      isEq' xts1 cod1 xts2 cod2
    ((_, WeakTermPiIntro _ kind1 xts1 e1), (_, WeakTermPiIntro _ kind2 xts2 e2)) ->
      isEq' (catMaybes [fromLamKind kind1] ++ xts1) e1 (catMaybes [fromLamKind kind2] ++ xts2) e2
    -- ((_, WeakTermPiIntro mName1 xts1 e1), (_, WeakTermPiIntro mName2 xts2 e2))
    --   | mName1 == mName2 ->
    --     isEq' xts1 e1 xts2 e2
    ((_, WeakTermPiElim e1 es1), (_, WeakTermPiElim e2 es2)) -> do
      b1 <- isEq e1 e2
      b2 <- and <$> zipWithM isEq es1 es2
      return $ b1 && b2
    -- ((_, WeakTermFix _ self1 xts1 e1), (_, WeakTermFix _ self2 xts2 e2)) ->
    --   isEq' (self1 : xts1) e1 (self2 : xts2) e2
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
      let sub' = IntMap.insert (asInt x2) (m1, WeakTermVar VarKindLocal x1) sub
      b2 <- isEq'' sub' rest1 cod1 rest2 cod2
      return $ b1 && b2
    _ ->
      return False
