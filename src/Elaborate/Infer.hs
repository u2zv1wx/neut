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
import Data.Basic
import Data.Env
import qualified Data.HashMap.Lazy as Map
import qualified Data.IntMap as IntMap
import Data.Log
import Data.LowType
import qualified Data.Set as S
import Data.Term
import qualified Data.Text as T
import Data.WeakTerm
import Reduce.WeakTerm

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
      -- return ((m, WeakTermUpsilon x), t)
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
      | Just _ <- asLowInt x ->
        return ((m, WeakTermConst x), (m, WeakTermTau))
      | Just _ <- asLowFloat x ->
        return ((m, WeakTermConst x), (m, WeakTermTau))
      | Just op <- asPrimOp x ->
        inferExternal m x (primOpToType m op)
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
    (m, WeakTermEnumElim (e, _) ces) -> do
      -- tEnum <- inferType' ctx t
      (e', t') <- infer' ctx e
      -- insConstraintEnv tEnum t'
      if null ces
        then do
          h <- newTypeAsterInCtx ctx m
          return ((m, WeakTermEnumElim (e', t') []), h) -- ex falso quodlibet
        else do
          let (cs, es) = unzip ces
          (cs', tcs) <- unzip <$> mapM (inferEnumCase ctx) cs
          forM_ (zip (repeat t') tcs) $ uncurry insConstraintEnv
          (es', ts) <- unzip <$> mapM (infer' ctx) es
          -- let tHead = head ts
          forM_ (zip (repeat (head ts)) (tail ts)) $ uncurry insConstraintEnv
          -- constrainList ts
          return ((m, WeakTermEnumElim (e', t') $ zip cs' es'), head ts)
    (m, WeakTermTensor ts) -> do
      ts' <- mapM (inferType' ctx) ts
      return ((m, WeakTermTensor ts'), (m, WeakTermTau))
    (m, WeakTermTensorIntro es) -> do
      (es', ts') <- unzip <$> mapM (infer' ctx) es
      return ((m, WeakTermTensorIntro es'), (m, WeakTermTensor ts'))
    (m, WeakTermTensorElim xts e1 e2) -> do
      (e1', t1) <- infer' ctx e1
      (xts', (e2', t2)) <- inferBinder ctx xts e2
      let ts = map (\(_, _, t) -> t) xts'
      insConstraintEnv (m, WeakTermTensor ts) t1
      return ((m, WeakTermTensorElim xts' e1' e2'), t2)
    (m, WeakTermQuestion e _) -> do
      (e', te) <- infer' ctx e
      return ((m, WeakTermQuestion e' te), te)
    (m, WeakTermDerangement kind resultType ekts) -> do
      resultType' <- inferType' ctx resultType
      let (es, ks, _) = unzip3 ekts
      (es', ts') <- unzip <$> mapM (infer' ctx) es
      let borrowedTypes = takeBorrowedTypes $ zip ts' ks
      productType <- productTypeOf m (borrowedTypes ++ [resultType'])
      return ((m, WeakTermDerangement kind resultType' (zip3 es' ks ts')), productType)

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
      insConstraintEnv tx t
      let sub = IntMap.singleton (asInt x) e
      (xts', cod') <- substWeakTermPlus'' sub IntMap.empty xts cod
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
  insConstraintEnv (metaOf t, WeakTermTau) u
  return t'

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
      ys <- mapM (const $ newIdentFromText "arg") es
      yts <- newTypeAsterListInCtx ctx $ zip ys (map metaOf es)
      cod <- newTypeAsterInCtx (ctx ++ yts) m
      insConstraintEnv (metaOf e, WeakTermPi yts cod) t
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
  let varSeq = map (\(mx, x, _) -> (mx, WeakTermUpsilon x)) ctx
  -- let varSeq = map (\(_, x, _) -> (m, WeakTermUpsilon x)) ctx
  let higherApp = (m, WeakTermPiElim higherAster varSeq)
  aster <- newAster m
  let app = (m, WeakTermPiElim aster varSeq)
  return (app, higherApp)

-- In a context (x1 : A1, ..., xn : An), this function creates a metavariable
--   ?M  : Pi (x1 : A1, ..., xn : An). Univ{i}
-- and return ?M @ (x1, ..., xn) : Univ{i}.
newTypeAsterInCtx :: Context -> Hint -> WithEnv WeakTermPlus
newTypeAsterInCtx ctx m = do
  let varSeq = map (\(mx, x, _) -> (mx, WeakTermUpsilon x)) ctx
  -- let varSeq = map (\(_, x, _) -> (m, WeakTermUpsilon x)) ctx
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

-- constrainList :: [WeakTermPlus] -> WithEnv ()
-- constrainList typeList =
--   case typeList of
--     [] ->
--       return ()
--     [_] ->
--       return ()
--     (t1 : t2 : ts) -> do
--       insConstraintEnv t1 t2
--       constrainList $ t2 : ts

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

lookupKind :: Hint -> T.Text -> WithEnv T.Text
lookupKind m name = do
  renv <- gets revEnumEnv
  case Map.lookup name renv of
    Nothing ->
      raiseError m $ "no such enum-intro is defined: " <> name
    Just (j, _) ->
      return j

-- A1 * ... * An := Pi (z : tau, k : Pi (_ : A1, ..., _ : An).Z). Z
productTypeOf :: Hint -> [WeakTermPlus] -> WithEnv WeakTermPlus
productTypeOf m ts =
  case ts of
    [t] ->
      return t
    _ -> do
      xs <- mapM (const $ newIdentFromText "_") ts
      let xts = zipWith (\x t -> (m, x, t)) xs ts
      weakTermSigma m xts

takeBorrowedTypes :: [(WeakTermPlus, DerangementArg)] -> [WeakTermPlus]
takeBorrowedTypes tks =
  case tks of
    [] ->
      []
    ((t, k) : rest) ->
      case k of
        DerangementArgLinear ->
          t : takeBorrowedTypes rest
        DerangementArgAffine ->
          takeBorrowedTypes rest

weakTermSigma :: Hint -> [WeakIdentPlus] -> WithEnv WeakTermPlus
weakTermSigma m xts = do
  z <- newIdentFromText "internal.sigma-tau"
  let vz = (m, WeakTermUpsilon z)
  k <- newIdentFromText "sigma"
  return (m, WeakTermPi [(m, z, (m, WeakTermTau)), (m, k, (m, WeakTermPi xts vz))] vz)

lookupConstTypeEnv :: Hint -> T.Text -> WithEnv TermPlus
lookupConstTypeEnv m x
  | Just _ <- asLowTypeMaybe x =
    return (m, TermTau)
  | Just op <- asPrimOp x =
    primOpToType m op
  | otherwise = do
    ctenv <- gets constTypeEnv
    case Map.lookup x ctenv of
      Just t ->
        return t
      Nothing ->
        raiseCritical m $
          "the constant `" <> x <> "` is not found in the type environment."

primOpToType :: Hint -> PrimOp -> WithEnv TermPlus
primOpToType m (PrimOp op domList cod) = do
  domList' <- mapM (lowTypeToType m) domList
  xs <- mapM (const (newIdentFromText "_")) domList'
  let xts = zipWith (\x t -> (m, x, t)) xs domList'
  if S.member op cmpOpSet
    then do
      let cod' = (m, TermEnum "bool")
      return (m, TermPi xts cod')
    else do
      cod' <- lowTypeToType m cod
      return (m, TermPi xts cod')
