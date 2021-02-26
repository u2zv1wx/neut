module Elaborate.Infer
  ( infer,
    inferType,
    insConstraintEnv,
    insWeakTypeEnv,
    newTypeAsterInCtx,
    Context,
  )
where

import Control.Monad.State.Lazy
import Data.ConstType
import Data.EnumCase
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Hint
import Data.Ident
import qualified Data.IntMap as IntMap
import Data.Log
import Data.LowType
import Data.Primitive
import Data.Term
import qualified Data.Text as T
import Data.WeakTerm

type Context = [WeakIdentPlus]

infer :: WeakTermPlus -> WithEnv (WeakTermPlus, WeakTermPlus)
infer =
  infer' []

inferType :: WeakTermPlus -> WithEnv WeakTermPlus
inferType =
  inferType' []

infer' :: Context -> WeakTermPlus -> WithEnv (WeakTermPlus, WeakTermPlus)
infer' ctx term =
  case term of
    (m, WeakTermTau) ->
      return ((m, WeakTermTau), (m, WeakTermTau))
    (m, WeakTermUpsilon x) -> do
      t <- lookupWeakTypeEnv m x
      return ((m, WeakTermUpsilon x), (m, snd t))
    (m, WeakTermPi xts t) -> do
      (xts', t') <- inferPi ctx xts t
      return ((m, WeakTermPi xts' t'), (m, WeakTermTau))
    (m, WeakTermPiIntro xts e) -> do
      (xts', (e', t')) <- inferBinder ctx xts e
      return ((m, WeakTermPiIntro xts' e'), (m, WeakTermPi xts' t'))
    (m, WeakTermPiElim e es) -> do
      etls <- mapM (infer' ctx) es
      etl <- infer' ctx e
      inferPiElim ctx m etl etls
    (m, WeakTermFix (mx, x, t) xts e) -> do
      t' <- inferType' ctx t
      insWeakTypeEnv x t'
      -- Note that we cannot extend context with x. The type of e cannot be dependent on `x`.
      -- Otherwise the type of `mu x. e` might have `x` as free variable, which is unsound.
      (xts', (e', tCod)) <- inferBinder ctx xts e
      let piType = (m, WeakTermPi xts' tCod)
      insConstraintEnv piType t'
      return ((m, WeakTermFix (mx, x, t') xts' e'), piType)
    (m, WeakTermAster _) -> do
      (app, higherApp) <- newAsterInCtx ctx m
      return (app, higherApp)
    (m, WeakTermConst x)
      -- i64, f16, etc.
      | Just _ <- asLowTypeMaybe x ->
        return ((m, WeakTermConst x), (m, WeakTermTau))
      | Just op <- asUnaryOpMaybe x ->
        inferExternal m x (unaryOpToType m op)
      | Just op <- asBinaryOpMaybe x ->
        inferExternal m x (binaryOpToType m op)
      | Just lt <- asArrayAccessMaybe x ->
        inferExternal m x (arrayAccessToType m lt)
      | otherwise -> do
        t <- lookupConstTypeEnv m x
        return ((m, WeakTermConst x), (m, snd $ weaken t))
    (m, WeakTermInt t i) -> do
      t' <- inferType' [] t -- ctx == [] since t' should be i64, i8, etc. (i.e. t must be closed)
      return ((m, WeakTermInt t' i), t')
    (m, WeakTermFloat t f) -> do
      t' <- inferType' [] t -- t must be closed
      return ((m, WeakTermFloat t' f), t')
    (m, WeakTermEnum name) ->
      return ((m, WeakTermEnum name), (m, WeakTermTau))
    (m, WeakTermEnumIntro l) -> do
      k <- lookupKind m l
      let t = (m, WeakTermEnum k)
      return ((m, WeakTermEnumIntro l), t)
    (m, WeakTermEnumElim (e, t) ces) -> do
      tEnum <- inferType' ctx t
      (e', t') <- infer' ctx e
      insConstraintEnv tEnum t'
      if null ces
        then do
          h <- newTypeAsterInCtx ctx m
          return ((m, WeakTermEnumElim (e', t') []), h) -- ex falso quodlibet
        else do
          let (cs, es) = unzip ces
          (cs', tcs) <- unzip <$> mapM (inferEnumCase ctx) cs
          forM_ (zip (repeat t') tcs) $ uncurry insConstraintEnv
          (es', ts) <- unzip <$> mapM (infer' ctx) es
          constrainList ts
          return ((m, WeakTermEnumElim (e', t') $ zip cs' es'), head ts)
    (m, WeakTermArray dom k) -> do
      (dom', tDom) <- infer' ctx dom
      let tDom' = i64 m
      insConstraintEnv tDom tDom'
      return ((m, WeakTermArray dom' k), (m, WeakTermTau))
    (m, WeakTermArrayIntro k es) -> do
      tCod <- inferWeakKind m k
      (es', ts) <- unzip <$> mapM (infer' ctx) es
      forM_ (zip ts (repeat tCod)) $ uncurry insConstraintEnv
      let len = toInteger $ length es
      let dom = (m, WeakTermInt (i64 m) len)
      let t = (m, WeakTermArray dom k)
      return ((m, WeakTermArrayIntro k es'), t)
    (m, WeakTermArrayElim k xts e1 e2) -> do
      (e1', t1) <- infer' ctx e1
      (xts', (e2', t2)) <- inferBinder ctx xts e2
      let len = toInteger $ length xts
      let dom = (m, WeakTermInt (i64 m) len)
      insConstraintEnv t1 (fst e1', WeakTermArray dom k)
      let ts = map (\(_, _, t) -> t) xts'
      tCod <- inferWeakKind m k
      forM_ (zip ts (repeat tCod)) $ uncurry insConstraintEnv
      return ((m, WeakTermArrayElim k xts' e1' e2'), t2)
    (m, WeakTermStruct ts) ->
      return ((m, WeakTermStruct ts), (m, WeakTermTau))
    (m, WeakTermStructIntro eks) -> do
      let (es, ks) = unzip eks
      ts <- mapM (inferWeakKind m) ks
      let structType = (m, WeakTermStruct ks)
      (es', ts') <- unzip <$> mapM (infer' ctx) es
      forM_ (zip ts' ts) $ uncurry insConstraintEnv
      return ((m, WeakTermStructIntro $ zip es' ks), structType)
    (m, WeakTermStructElim xks e1 e2) -> do
      (e1', t1) <- infer' ctx e1
      let (ms, xs, ks) = unzip3 xks
      ts <- mapM (inferWeakKind m) ks
      let structType = (fst e1', WeakTermStruct ks)
      insConstraintEnv t1 structType
      forM_ (zip xs ts) $ uncurry insWeakTypeEnv
      (e2', t2) <- infer' (ctx ++ zip3 ms xs ts) e2
      return ((m, WeakTermStructElim xks e1' e2'), t2)
    (m, WeakTermQuestion e _) -> do
      (e', te) <- infer' ctx e
      return ((m, WeakTermQuestion e' te), te)

-- (_, WeakTermErase _ e) ->
--   infer' ctx e

inferArgs ::
  Hint ->
  [(WeakTermPlus, WeakTermPlus)] ->
  [WeakIdentPlus] ->
  WeakTermPlus ->
  WithEnv WeakTermPlus
inferArgs m args1 args2 cod =
  case (args1, args2) of
    ([], []) ->
      return cod
    ((e, t) : ets, (_, x, tx) : xts) -> do
      insConstraintEnv t tx
      let sub = IntMap.singleton (asInt x) e
      let (xts', cod') = substWeakTermPlus'' sub xts cod
      inferArgs m ets xts' cod'
    _ ->
      raiseCritical m "invalid argument passed to inferArgs"

inferExternal :: Hint -> T.Text -> WithEnv TermPlus -> WithEnv (WeakTermPlus, WeakTermPlus)
inferExternal m x comp = do
  t <- comp
  return ((m, WeakTermConst x), (m, snd $ weaken t))

inferType' :: Context -> WeakTermPlus -> WithEnv WeakTermPlus
inferType' ctx t = do
  (t', u) <- infer' ctx t
  insConstraintEnv u (metaOf t, WeakTermTau)
  return t'

inferWeakKind :: Hint -> ArrayKind -> WithEnv WeakTermPlus
inferWeakKind m kind =
  weaken <$> inferKind m kind

inferPi ::
  Context ->
  [WeakIdentPlus] ->
  WeakTermPlus ->
  WithEnv ([WeakIdentPlus], WeakTermPlus)
inferPi ctx binder cod =
  case binder of
    [] -> do
      (cod', mlPiCod) <- inferType' ctx cod
      return ([], (cod', mlPiCod))
    ((mx, x, t) : xts) -> do
      t' <- inferType' ctx t
      insWeakTypeEnv x t'
      (xtls', tlCod) <- inferPi (ctx ++ [(mx, x, t')]) xts cod
      return ((mx, x, t') : xtls', tlCod)

inferBinder ::
  Context ->
  [WeakIdentPlus] ->
  WeakTermPlus ->
  WithEnv ([WeakIdentPlus], (WeakTermPlus, WeakTermPlus))
inferBinder ctx binder e =
  case binder of
    [] -> do
      etl' <- infer' ctx e
      return ([], etl')
    ((mx, x, t) : xts) -> do
      t' <- inferType' ctx t
      insWeakTypeEnv x t'
      (xts', etl') <- inferBinder (ctx ++ [(mx, x, t')]) xts e
      return ((mx, x, t') : xts', etl')

inferPiElim ::
  Context ->
  Hint ->
  (WeakTermPlus, WeakTermPlus) ->
  [(WeakTermPlus, WeakTermPlus)] ->
  WithEnv (WeakTermPlus, WeakTermPlus)
inferPiElim ctx m (e, t) ets = do
  let es = map fst ets
  case t of
    (_, WeakTermPi xts cod)
      | length xts == length ets -> do
        cod' <- inferArgs m ets xts cod
        return ((m, WeakTermPiElim e es), cod')
    _ -> do
      ys <- mapM (const $ newNameWith' "arg") es
      yts <- newTypeAsterListInCtx ctx $ zip ys (map metaOf es)
      cod <- newTypeAsterInCtx (ctx ++ yts) m
      insConstraintEnv t (metaOf e, WeakTermPi yts cod)
      cod' <- inferArgs m ets yts cod
      return ((m, WeakTermPiElim e es), cod')

-- In a context (x1 : A1, ..., xn : An), this function creates metavariables
--   ?M  : Pi (x1 : A1, ..., xn : An). ?Mt @ (x1, ..., xn)
--   ?Mt : Pi (x1 : A1, ..., xn : An). Univ
-- and return ?M @ (x1, ..., xn) : ?Mt @ (x1, ..., xn).
-- Note that we can't just set `?M : Pi (x1 : A1, ..., xn : An). Univ` since
-- WeakTermAster might be used as an ordinary term, that is, a term which is not a type.
newAsterInCtx :: Context -> Hint -> WithEnv (WeakTermPlus, WeakTermPlus)
newAsterInCtx ctx m = do
  higherAster <- newAster m
  let varSeq = map (\(_, x, _) -> (m, WeakTermUpsilon x)) ctx
  let higherApp = (m, WeakTermPiElim higherAster varSeq)
  aster <- newAster m
  let app = (m, WeakTermPiElim aster varSeq)
  return (app, higherApp)

-- In a context (x1 : A1, ..., xn : An), this function creates a metavariable
--   ?M  : Pi (x1 : A1, ..., xn : An). Univ{i}
-- and return ?M @ (x1, ..., xn) : Univ{i}.
newTypeAsterInCtx :: Context -> Hint -> WithEnv WeakTermPlus
newTypeAsterInCtx ctx m = do
  let varSeq = map (\(_, x, _) -> (m, WeakTermUpsilon x)) ctx
  aster <- newAster m
  return (m, WeakTermPiElim aster varSeq)

-- In context ctx == [x1, ..., xn], `newTypeAsterListInCtx ctx [y1, ..., ym]` generates
-- the following list:
--
--   [(y1,   ?M1   @ (x1, ..., xn)),
--    (y2,   ?M2   @ (x1, ..., xn, y1),
--    ...,
--    (y{m}, ?M{m} @ (x1, ..., xn, y1, ..., y{m-1}))]
--
-- inserting type information `yi : ?Mi @ (x1, ..., xn, y1, ..., y{i-1})
newTypeAsterListInCtx :: Context -> [(Ident, Hint)] -> WithEnv [WeakIdentPlus]
newTypeAsterListInCtx ctx ids =
  case ids of
    [] ->
      return []
    ((x, m) : rest) -> do
      t <- newTypeAsterInCtx ctx m
      insWeakTypeEnv x t
      ts <- newTypeAsterListInCtx (ctx ++ [(m, x, t)]) rest
      return $ (m, x, t) : ts

inferEnumCase :: Context -> EnumCasePlus -> WithEnv (EnumCasePlus, WeakTermPlus)
inferEnumCase ctx weakCase =
  case weakCase of
    (m, EnumCaseLabel name) -> do
      k <- lookupKind m name
      return (weakCase, (m, WeakTermEnum k))
    (m, EnumCaseDefault) -> do
      h <- newTypeAsterInCtx ctx m
      return ((m, EnumCaseDefault), h)

constrainList :: [WeakTermPlus] -> WithEnv ()
constrainList typeList =
  case typeList of
    [] ->
      return ()
    [_] ->
      return ()
    (t1 : t2 : ts) -> do
      insConstraintEnv t1 t2
      constrainList $ t2 : ts

insConstraintEnv :: WeakTermPlus -> WeakTermPlus -> WithEnv ()
insConstraintEnv t1 t2 =
  modify (\e -> e {constraintEnv = (t1, t2) : constraintEnv e})

insWeakTypeEnv :: Ident -> WeakTermPlus -> WithEnv ()
insWeakTypeEnv (I (_, i)) t =
  modify (\e -> e {weakTypeEnv = IntMap.insert i t (weakTypeEnv e)})

lookupWeakTypeEnv :: Hint -> Ident -> WithEnv WeakTermPlus
lookupWeakTypeEnv m s = do
  mt <- lookupWeakTypeEnvMaybe s
  case mt of
    Just t ->
      return t
    Nothing ->
      raiseCritical m $
        asText' s <> " is not found in the weak type environment."

lookupWeakTypeEnvMaybe :: Ident -> WithEnv (Maybe WeakTermPlus)
lookupWeakTypeEnvMaybe (I (_, s)) = do
  wtenv <- gets weakTypeEnv
  case IntMap.lookup s wtenv of
    Nothing ->
      return Nothing
    Just t ->
      return $ Just t

-- lookupKind :: Hint -> T.Text -> WithEnv T.Text
-- lookupKind m name = do
--   renv <- gets revEnumEnv
--   case Map.lookup name renv of
--     Nothing ->
--       raiseError m $ "no such enum-intro is defined: " <> name
--     Just (j, _) ->
--       return j

lookupKind :: Hint -> T.Text -> WithEnv T.Text
lookupKind m name = do
  renv <- gets revEnumEnv
  case Map.lookup name renv of
    Nothing ->
      raiseError m $ "no such enum-intro is defined: " <> name
    Just (j, _) ->
      return j
