module Elaborate.Infer
  ( infer,
    inferType,
    insConstraintEnv,
    insWeakTypeEnv,
  )
where

import Control.Monad
import Data.Basic
import Data.Global
import qualified Data.HashMap.Lazy as Map
import Data.IORef
import qualified Data.IntMap as IntMap
import Data.Log
import Data.LowType
import qualified Data.Set as S
import Data.Term
import qualified Data.Text as T
import Data.WeakTerm
import Reduce.WeakTerm

type Context = [WeakIdentPlus]

infer :: WeakTermPlus -> IO (WeakTermPlus, WeakTermPlus)
infer =
  infer' []

inferType :: WeakTermPlus -> IO WeakTermPlus
inferType =
  inferType' []

infer' :: Context -> WeakTermPlus -> IO (WeakTermPlus, WeakTermPlus)
infer' ctx term =
  case term of
    (m, WeakTermTau) ->
      return ((m, WeakTermTau), (m, WeakTermTau))
    (m, WeakTermVar kind x) -> do
      t <- lookupWeakTypeEnv m x
      return ((m, WeakTermVar kind x), (m, snd t))
    (m, WeakTermPi xts t) -> do
      (xts', t') <- inferPi ctx xts t
      return ((m, WeakTermPi xts' t'), (m, WeakTermTau))
    (m, WeakTermPiIntro opacity kind xts e) -> do
      case kind of
        LamKindFix (mx, x, t) -> do
          t' <- inferType' ctx t
          insWeakTypeEnv x t'
          (xts', (e', tCod)) <- inferBinder ctx xts e
          let piType = (m, WeakTermPi xts' tCod)
          insConstraintEnv piType t'
          return ((m, WeakTermPiIntro opacity (LamKindFix (mx, x, t')) xts' e'), piType)
        _ -> do
          (xts', (e', t')) <- inferBinder ctx xts e
          return ((m, WeakTermPiIntro opacity kind xts' e'), (m, WeakTermPi xts' t'))
    (m, WeakTermPiElim e es) -> do
      etls <- mapM (infer' ctx) es
      etl <- infer' ctx e
      inferPiElim ctx m etl etls
    (m, WeakTermAster x) -> do
      henv <- readIORef holeEnv
      case IntMap.lookup x henv of
        Just asterInfo ->
          return asterInfo
        Nothing -> do
          (app, higherApp) <- newAsterInCtx ctx m
          modifyIORef' holeEnv $ \env -> IntMap.insert x (app, higherApp) env
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
    (m, WeakTermEnum path name) ->
      return ((m, WeakTermEnum path name), (m, WeakTermTau))
    (m, WeakTermEnumIntro path l) -> do
      k <- lookupKind m l
      let t = (m, WeakTermEnum path k)
      return ((m, WeakTermEnumIntro path l), t)
    (m, WeakTermEnumElim (e, _) ces) -> do
      (e', t') <- infer' ctx e
      let (cs, es) = unzip ces
      (cs', tcs) <- unzip <$> mapM (inferEnumCase ctx) cs
      forM_ (zip tcs (repeat t')) $ uncurry insConstraintEnv
      (es', ts) <- unzip <$> mapM (infer' ctx) es
      h <- newTypeAsterInCtx ctx m
      forM_ (zip (repeat h) ts) $ uncurry insConstraintEnv
      return ((m, WeakTermEnumElim (e', t') $ zip cs' es'), h)
    (m, WeakTermQuestion e _) -> do
      (e', te) <- infer' ctx e
      return ((m, WeakTermQuestion e' te), te)
    (m, WeakTermDerangement kind es) -> do
      resultType <- newTypeAsterInCtx ctx m
      (es', _) <- unzip <$> mapM (infer' ctx) es
      return ((m, WeakTermDerangement kind es'), resultType)
    (m, WeakTermCase _ mSubject (e, _) clauseList) -> do
      resultType <- newTypeAsterInCtx ctx m
      (e', t') <- infer' ctx e
      mSubject' <- mapM (inferSubject m ctx) mSubject
      case clauseList of
        [] ->
          return ((m, WeakTermCase resultType mSubject' (e', t') []), resultType) -- ex falso quodlibet
        ((_, constructorName, _), _) : _ -> do
          cenv <- readIORef constructorEnv
          case Map.lookup (asText constructorName) cenv of
            Nothing ->
              raiseCritical m $ "no such constructor defined (infer): " <> asText constructorName
            Just (holeCount, _) -> do
              holeList <- mapM (const $ newAsterInCtx ctx m) $ replicate holeCount ()
              clauseList' <- forM clauseList $ \((mPat, name, xts), body) -> do
                (xts', (body', tBody)) <- inferBinder ctx xts body
                insConstraintEnv resultType tBody
                let xs = map (\(mx, x, t) -> ((mx, WeakTermVar VarKindLocal x), t)) xts'
                tCons <- lookupWeakTypeEnv m name
                case holeList ++ xs of
                  [] ->
                    insConstraintEnv tCons t'
                  _ -> do
                    (_, tPat) <- inferPiElim ctx m ((m, WeakTermVar VarKindLocal name), tCons) (holeList ++ xs)
                    insConstraintEnv tPat t'
                return ((mPat, name, xts'), body')
              return ((m, WeakTermCase resultType mSubject' (e', t') clauseList'), resultType)
    (m, WeakTermIgnore e) -> do
      (e', t') <- infer' ctx e
      return ((m, WeakTermIgnore e'), t')

inferSubject :: Hint -> Context -> WeakTermPlus -> IO WeakTermPlus
inferSubject m ctx subject = do
  (subject', tSub) <- infer' ctx subject
  insConstraintEnv (m, WeakTermTau) tSub
  return subject'

inferArgs ::
  SubstWeakTerm ->
  Hint ->
  [(WeakTermPlus, WeakTermPlus)] ->
  [WeakIdentPlus] ->
  WeakTermPlus ->
  IO WeakTermPlus
inferArgs sub m args1 args2 cod =
  case (args1, args2) of
    ([], []) ->
      substWeakTermPlus sub cod
    ((e, t) : ets, (_, x, tx) : xts) -> do
      tx' <- substWeakTermPlus sub tx
      t' <- substWeakTermPlus sub t
      insConstraintEnv tx' t'
      inferArgs (IntMap.insert (asInt x) e sub) m ets xts cod
    _ ->
      raiseCritical m "invalid argument passed to inferArgs"

inferExternal :: Hint -> T.Text -> IO TermPlus -> IO (WeakTermPlus, WeakTermPlus)
inferExternal m x comp = do
  t <- comp
  return ((m, WeakTermConst x), (m, snd $ weaken t))

inferType' :: Context -> WeakTermPlus -> IO WeakTermPlus
inferType' ctx t = do
  (t', u) <- infer' ctx t
  insConstraintEnv (metaOf t, WeakTermTau) u
  return t'

inferPi ::
  Context ->
  [WeakIdentPlus] ->
  WeakTermPlus ->
  IO ([WeakIdentPlus], WeakTermPlus)
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
  IO ([WeakIdentPlus], (WeakTermPlus, WeakTermPlus))
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
  IO (WeakTermPlus, WeakTermPlus)
inferPiElim ctx m (e, t) ets = do
  let es = map fst ets
  case t of
    (_, WeakTermPi xts (_, cod))
      | length xts == length ets -> do
        cod' <- inferArgs IntMap.empty m ets xts (m, cod)
        -- cod' <- inferArgs m ets xts (m, cod)
        return ((m, WeakTermPiElim e es), cod')
    _ -> do
      ys <- mapM (const $ newIdentFromText "arg") es
      yts <- newTypeAsterListInCtx ctx $ zip ys (map metaOf es)
      cod <- newTypeAsterInCtx (ctx ++ yts) m
      insConstraintEnv (metaOf e, WeakTermPi yts cod) t
      cod' <- inferArgs IntMap.empty m ets yts cod
      -- cod' <- inferArgs m ets yts cod
      return ((m, WeakTermPiElim e es), cod')

-- In a context (x1 : A1, ..., xn : An), this function creates metavariables
--   ?M  : Pi (x1 : A1, ..., xn : An). ?Mt @ (x1, ..., xn)
--   ?Mt : Pi (x1 : A1, ..., xn : An). Univ
-- and return ?M @ (x1, ..., xn) : ?Mt @ (x1, ..., xn).
-- Note that we can't just set `?M : Pi (x1 : A1, ..., xn : An). Univ` since
-- WeakTermAster might be used as an ordinary term, that is, a term which is not a type.
newAsterInCtx :: Context -> Hint -> IO (WeakTermPlus, WeakTermPlus)
newAsterInCtx ctx m = do
  higherAster <- newAster m
  let varSeq = map (\(mx, x, _) -> (mx, WeakTermVar VarKindLocal x)) ctx
  let higherApp = (m, WeakTermPiElim higherAster varSeq)
  aster <- newAster m
  let app = (m, WeakTermPiElim aster varSeq)
  return (app, higherApp)

-- In a context (x1 : A1, ..., xn : An), this function creates a metavariable
--   ?M  : Pi (x1 : A1, ..., xn : An). Univ{i}
-- and return ?M @ (x1, ..., xn) : Univ{i}.
newTypeAsterInCtx :: Context -> Hint -> IO WeakTermPlus
newTypeAsterInCtx ctx m = do
  let varSeq = map (\(mx, x, _) -> (mx, WeakTermVar VarKindLocal x)) ctx
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
newTypeAsterListInCtx :: Context -> [(Ident, Hint)] -> IO [WeakIdentPlus]
newTypeAsterListInCtx ctx ids =
  case ids of
    [] ->
      return []
    ((x, m) : rest) -> do
      t <- newTypeAsterInCtx ctx m
      insWeakTypeEnv x t
      ts <- newTypeAsterListInCtx (ctx ++ [(m, x, t)]) rest
      return $ (m, x, t) : ts

inferEnumCase :: Context -> EnumCasePlus -> IO (EnumCasePlus, WeakTermPlus)
inferEnumCase ctx weakCase =
  case weakCase of
    (m, EnumCaseLabel path name) -> do
      k <- lookupKind m name
      return (weakCase, (m, WeakTermEnum path k))
    (m, EnumCaseDefault) -> do
      h <- newTypeAsterInCtx ctx m
      return ((m, EnumCaseDefault), h)
    (m, EnumCaseInt _) -> do
      raiseCritical m "enum-case-int shouldn't be used in the target language"

insConstraintEnv :: WeakTermPlus -> WeakTermPlus -> IO ()
insConstraintEnv t1 t2 =
  modifyIORef' constraintEnv $ \env -> (t1, t2) : env

insWeakTypeEnv :: Ident -> WeakTermPlus -> IO ()
insWeakTypeEnv (I (_, i)) t =
  modifyIORef' weakTypeEnv $ \env -> IntMap.insert i t env

lookupWeakTypeEnv :: Hint -> Ident -> IO WeakTermPlus
lookupWeakTypeEnv m s = do
  mt <- lookupWeakTypeEnvMaybe s
  case mt of
    Just t ->
      return t
    Nothing ->
      raiseCritical m $
        asText' s <> " is not found in the weak type environment."

lookupWeakTypeEnvMaybe :: Ident -> IO (Maybe WeakTermPlus)
lookupWeakTypeEnvMaybe (I (_, s)) = do
  wtenv <- readIORef weakTypeEnv
  case IntMap.lookup s wtenv of
    Nothing ->
      return Nothing
    Just t ->
      return $ Just t

lookupKind :: Hint -> T.Text -> IO T.Text
lookupKind m name = do
  renv <- readIORef revEnumEnv
  case Map.lookup name renv of
    Nothing ->
      raiseError m $ "no such enum-intro is defined: " <> name
    Just (_, j, _) ->
      return j

lookupConstTypeEnv :: Hint -> T.Text -> IO TermPlus
lookupConstTypeEnv m x
  | Just _ <- asLowTypeMaybe x =
    return (m, TermTau)
  | Just op <- asPrimOp x =
    primOpToType m op
  | otherwise = do
    ctenv <- readIORef constTypeEnv
    case Map.lookup x ctenv of
      Just t ->
        return t
      Nothing ->
        raiseCritical m $
          "the constant `" <> x <> "` is not found in the type environment."

primOpToType :: Hint -> PrimOp -> IO TermPlus
primOpToType m (PrimOp op domList cod) = do
  domList' <- mapM (lowTypeToType m) domList
  xs <- mapM (const (newIdentFromText "_")) domList'
  let xts = zipWith (\x t -> (m, x, t)) xs domList'
  if S.member op cmpOpSet
    then do
      path <- getExecPath
      let cod' = (m, TermEnum path "bool")
      return (m, TermPi xts cod')
    else do
      cod' <- lowTypeToType m cod
      return (m, TermPi xts cod')
