module Elaborate.Unify
  ( unify,
  )
where

import Control.Exception.Safe
import Control.Monad
import Data.Basic
import Data.Env
import Data.IORef
import qualified Data.IntMap as IntMap
import Data.Log
import qualified Data.PQueue.Min as Q
import qualified Data.Set as S
import qualified Data.Text as T
import Data.WeakTerm
import Reduce.WeakTerm

data Stuck
  = StuckPiElimVar Ident [(Hint, [WeakTermPlus])]
  | StuckPiElimVarOpaque Ident [(Hint, [WeakTermPlus])]
  | StuckPiElimAster Int [[WeakTermPlus]]
  deriving (Show)

unify :: IO ()
unify =
  analyze >> synthesize

analyze :: IO ()
analyze = do
  cs <- readIORef constraintEnv
  modifyIORef' constraintEnv $ \_ -> []
  simplify $ zip cs cs

synthesize :: IO ()
synthesize = do
  cs <- readIORef suspendedConstraintEnv
  case Q.minView cs of
    Nothing ->
      return ()
    Just ((SuspendedConstraint (_, ConstraintKindDelta c, (_, orig))), cs') -> do
      modifyIORef' suspendedConstraintEnv $ \_ -> cs'
      simplify [(c, orig)]
      synthesize
    Just ((SuspendedConstraint (_, ConstraintKindOther, _)), _) ->
      throwTypeErrors

throwTypeErrors :: IO a
throwTypeErrors = do
  q <- readIORef suspendedConstraintEnv
  sub <- readIORef substEnv
  errorList <- forM (Q.toList q) $ \(SuspendedConstraint (_, _, (_, (expected, actual)))) -> do
    expected' <- substWeakTermPlus sub expected >>= reduceWeakTermPlus
    actual' <- substWeakTermPlus sub actual >>= reduceWeakTermPlus
    return $ logError (getPosInfo (fst actual)) $ constructErrorMsg actual' expected'
  throw $ Error errorList

constructErrorMsg :: WeakTermPlus -> WeakTermPlus -> T.Text
constructErrorMsg e1 e2 =
  "couldn't verify the definitional equality of the following two terms:\n- "
    <> toText e1
    <> "\n- "
    <> toText e2

simplify :: [(Constraint, Constraint)] -> IO ()
simplify constraintList =
  case constraintList of
    [] ->
      return ()
    headConstraint@(c, orig) : cs -> do
      expected <- reduceWeakTermPlus $ fst c
      actual <- reduceWeakTermPlus $ snd c
      case (expected, actual) of
        ((_, WeakTermTau), (_, WeakTermTau)) ->
          simplify cs
        ((_, WeakTermVar kind1 x1), (_, WeakTermVar kind2 x2))
          | kind1 == kind2,
            x1 == x2 ->
            simplify cs
        ((m1, WeakTermPi xts1 cod1), (m2, WeakTermPi xts2 cod2))
          | length xts1 == length xts2 -> do
            xt1 <- asWeakIdentPlus m1 cod1
            xt2 <- asWeakIdentPlus m2 cod2
            cs' <- simplifyBinder orig (xts1 ++ [xt1]) (xts2 ++ [xt2])
            simplify $ cs' ++ cs
        ((m1, WeakTermPiIntro _ kind1 xts1 e1), (m2, WeakTermPiIntro _ kind2 xts2 e2))
          | LamKindFix xt1@(_, x1, _) <- kind1,
            LamKindFix xt2@(_, x2, _) <- kind2,
            x1 == x2,
            length xts1 == length xts2 -> do
            yt1 <- asWeakIdentPlus m1 e1
            yt2 <- asWeakIdentPlus m2 e2
            cs' <- simplifyBinder orig (xt1 : xts1 ++ [yt1]) (xt2 : xts2 ++ [yt2])
            simplify $ cs' ++ cs
          | lamKindWeakEq kind1 kind2,
            length xts1 == length xts2 -> do
            xt1 <- asWeakIdentPlus m1 e1
            xt2 <- asWeakIdentPlus m2 e2
            cs' <- simplifyBinder orig (xts1 ++ [xt1]) (xts2 ++ [xt2])
            simplify $ cs' ++ cs
        ((_, WeakTermAster h1), (_, WeakTermAster h2))
          | h1 == h2 ->
            simplify cs
        ((_, WeakTermConst a1), (_, WeakTermConst a2))
          | a1 == a2 ->
            simplify cs
        ((_, WeakTermInt t1 l1), (_, WeakTermInt t2 l2))
          | l1 == l2 ->
            simplify $ ((t1, t2), orig) : cs
        ((_, WeakTermFloat t1 l1), (_, WeakTermFloat t2 l2))
          | l1 == l2 ->
            simplify $ ((t1, t2), orig) : cs
        ((_, WeakTermEnum a1), (_, WeakTermEnum a2))
          | a1 == a2 ->
            simplify cs
        ((_, WeakTermEnumIntro a1), (_, WeakTermEnumIntro a2))
          | a1 == a2 ->
            simplify cs
        ((_, WeakTermQuestion e1 t1), (_, WeakTermQuestion e2 t2)) ->
          simplify $ ((e1, e2), orig) : ((t1, t2), orig) : cs
        ((_, WeakTermDerangement i1 es1), (_, WeakTermDerangement i2 es2))
          | length es1 == length es2,
            i1 == i2 -> do
            simplify $ map (\pair -> (pair, orig)) (zip es1 es2) ++ cs
        (e1, e2) -> do
          sub <- readIORef substEnv
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
                    Just pairList <- asPairList (map snd mess1) (map snd mess2) -> do
                    simplify $ map (\pair -> (pair, orig)) pairList ++ cs
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
                    let uc = SuspendedConstraint (fmvs, ConstraintKindDelta (toPiElim lam mess1, e2), headConstraint)
                    modifyIORef' suspendedConstraintEnv $ \env -> Q.insert uc env
                    simplify cs
                (Just (StuckPiElimAster {}), Just (StuckPiElimVar x2 mess2))
                  | Just lam <- lookupDefinition x2 sub -> do
                    let uc = SuspendedConstraint (fmvs, ConstraintKindDelta (e1, toPiElim lam mess2), headConstraint)
                    modifyIORef' suspendedConstraintEnv $ \env -> Q.insert uc env
                    simplify cs
                (Just (StuckPiElimVar x1 mess1), _)
                  | Just lam <- lookupDefinition x1 sub -> do
                    simplify $ ((toPiElim lam mess1, e2), orig) : cs
                (_, Just (StuckPiElimVar x2 mess2))
                  | Just lam <- lookupDefinition x2 sub -> do
                    simplify $ ((e1, toPiElim lam mess2), orig) : cs
                _ -> do
                  let uc = SuspendedConstraint (fmvs, ConstraintKindOther, headConstraint)
                  modifyIORef' suspendedConstraintEnv $ \env -> Q.insert uc env
                  simplify cs

{-# INLINE resolveHole #-}
resolveHole :: Int -> [[WeakIdentPlus]] -> WeakTermPlus -> [(Constraint, Constraint)] -> IO ()
resolveHole h1 xss e2' cs = do
  modifyIORef' substEnv $ \env -> IntMap.insert h1 (toPiIntro xss e2') env
  sus <- readIORef suspendedConstraintEnv
  let (sus1, sus2) = Q.partition (\(SuspendedConstraint (hs, _, _)) -> S.member h1 hs) sus
  modifyIORef' suspendedConstraintEnv $ \_ -> sus2
  let sus1' = map (\(SuspendedConstraint (_, _, c)) -> c) $ Q.toList sus1
  simplify $ sus1' ++ cs

simplifyBinder :: Constraint -> [WeakIdentPlus] -> [WeakIdentPlus] -> IO [(Constraint, Constraint)]
simplifyBinder orig =
  simplifyBinder' orig IntMap.empty

simplifyBinder' :: Constraint -> SubstWeakTerm -> [WeakIdentPlus] -> [WeakIdentPlus] -> IO [(Constraint, Constraint)]
simplifyBinder' orig sub args1 args2 =
  case (args1, args2) of
    ((m1, x1, t1) : xts1, (_, x2, t2) : xts2) -> do
      t2' <- substWeakTermPlus sub t2
      let sub' = IntMap.insert (asInt x2) (m1, WeakTermVar VarKindLocal x1) sub
      rest <- simplifyBinder' orig sub' xts1 xts2
      return $ ((t1, t2'), orig) : rest
    _ ->
      return []

asWeakIdentPlus :: Hint -> WeakTermPlus -> IO WeakIdentPlus
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
