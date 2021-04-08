module Elaborate.Infer
  ( infer,
    inferType,
    insConstraintEnv,
    insWeakTypeEnv,
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
    (m, WeakTermVar _ x) -> do
      t <- lookupWeakTypeEnv m x
      senv <- gets substEnv
      oenv <- gets opaqueEnv
      case (IntMap.member (asInt x) senv, S.member x oenv) of
        (True, False) ->
          return ((m, WeakTermVar VarKindGlobalTransparent x), (m, snd t))
        (True, True) ->
          return ((m, WeakTermVar VarKindGlobalOpaque x), (m, snd t))
        (False, _) ->
          return ((m, WeakTermVar VarKindLocal x), (m, snd t))
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
      henv <- gets holeEnv
      case IntMap.lookup x henv of
        Just asterInfo ->
          return asterInfo
        Nothing -> do
          (app, higherApp) <- newAsterInCtx ctx m
          modify (\env -> env {holeEnv = IntMap.insert x (app, higherApp) henv})
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
      (e', t') <- infer' ctx e
      if null ces
        then do
          h <- newTypeAsterInCtx ctx m
          return ((m, WeakTermEnumElim (e', t') []), h) -- ex falso quodlibet
        else do
          let (cs, es) = unzip ces
          (cs', tcs) <- unzip <$> mapM (inferEnumCase ctx) cs
          forM_ (zip tcs (repeat t')) $ uncurry insConstraintEnv
          -- forM_ (zip (repeat t') tcs) $ uncurry insConstraintEnv
          (es', ts) <- unzip <$> mapM (infer' ctx) es
          forM_ (zip (repeat (head ts)) (tail ts)) $ uncurry insConstraintEnv
          return ((m, WeakTermEnumElim (e', t') $ zip cs' es'), head ts)
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
        ((constructorName, _), _) : _ -> do
          cenv <- gets constructorEnv
          case Map.lookup (asText constructorName) cenv of
            Nothing ->
              raiseCritical m $ "no such constructor defined (infer): " <> asText constructorName
            Just (holeCount, _) -> do
              holeList <- mapM (const $ newAsterInCtx ctx m) $ replicate holeCount ()
              clauseList' <- forM clauseList $ \((name, xts), body) -> do
                (xts', (body', tBody)) <- inferBinder ctx xts body
                insConstraintEnv resultType tBody
                let xs = map (\(mx, x, t) -> ((mx, WeakTermVar VarKindLocal x), t)) xts'
                tCons <- lookupWeakTypeEnv m name
                (_, tPat) <- inferPiElim ctx m ((m, WeakTermVar VarKindLocal name), tCons) (holeList ++ xs)
                insConstraintEnv tPat t'
                return ((name, xts'), body')
              return ((m, WeakTermCase resultType mSubject' (e', t') clauseList'), resultType)

inferSubject :: Hint -> Context -> WeakTermPlus -> WithEnv WeakTermPlus
inferSubject m ctx subject = do
  (subject', tSub) <- infer' ctx subject
  insConstraintEnv (m, WeakTermTau) tSub
  return subject'

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
    (_, WeakTermPi xts (_, cod))
      | length xts == length ets -> do
        cod' <- inferArgs m ets xts (m, cod)
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
  let varSeq = map (\(mx, x, _) -> (mx, WeakTermVar VarKindLocal x)) ctx
  -- let varSeq = map (\(_, x, _) -> (m, WeakTermVar x)) ctx
  let higherApp = (m, WeakTermPiElim higherAster varSeq)
  aster <- newAster m
  let app = (m, WeakTermPiElim aster varSeq)
  return (app, higherApp)

-- In a context (x1 : A1, ..., xn : An), this function creates a metavariable
--   ?M  : Pi (x1 : A1, ..., xn : An). Univ{i}
-- and return ?M @ (x1, ..., xn) : Univ{i}.
newTypeAsterInCtx :: Context -> Hint -> WithEnv WeakTermPlus
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
    (m, EnumCaseInt _) -> do
      raiseCritical m "enum-case-int shouldn't be used in the target language"

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
