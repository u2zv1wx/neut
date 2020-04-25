module Elaborate.Infer
  ( infer,
    inferType,
    inferSigma,
    insConstraintEnv,
    insWeakTypeEnv,
    newTypeHoleInCtx,
    Context,
  )
where

import Control.Monad.State.Lazy
import Data.EnumCase
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Ident
import qualified Data.IntMap as IntMap
import Data.LowType
import Data.Meta
import Data.Primitive
import Data.Size
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
    (m, WeakTermPi mName xts t) -> do
      (xts', t') <- inferPi ctx xts t
      return ((m, WeakTermPi mName xts' t'), (m, WeakTermTau))
    (m, WeakTermPiIntro info xts e) -> do
      (xts', (e', t')) <- inferBinder ctx xts e
      case info of
        Nothing ->
          return ((m, weakTermPiIntro xts' e'), (m, weakTermPi xts' t'))
        Just (indName, consName, args) -> do
          args' <- inferSigma ctx args
          return
            ( (m, WeakTermPiIntro (Just (indName, consName, args')) xts' e'),
              (m, WeakTermPi (Just $ asText indName) xts' t')
            )
    (m, WeakTermPiElim e es) -> do
      es' <- insertImplicits e es
      etls <- mapM (infer' ctx) es'
      etl <- infer' ctx e
      inferPiElim ctx m etl etls
    (m, WeakTermIter (mx, x, t) xts e) -> do
      t' <- inferType' ctx t
      insWeakTypeEnv x t'
      -- Note that we cannot extend context with x. The type of e cannot be dependent on `x`.
      -- Otherwise the type of `mu x. e` might have `x` as free variable, which is unsound.
      (xts', (e', tCod)) <- inferBinder ctx xts e
      let piType = (m, weakTermPi xts' tCod)
      insConstraintEnv piType t'
      return ((m, WeakTermIter (mx, x, t') xts' e'), piType)
    (m, WeakTermHole x) -> do
      zenv <- gets holeEnv
      case IntMap.lookup (asInt x) zenv of
        Just hole ->
          return hole
        Nothing -> do
          (app, higherApp) <- newHoleInCtx ctx m
          modify
            (\env -> env {holeEnv = IntMap.insert (asInt x) (app, higherApp) zenv})
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
    (m, WeakTermBoxElim _) ->
      raiseCritical m "`infer'` for box modality"
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
          h <- newTypeHoleInCtx ctx m
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
      -- let tDom' = (m, WeakTermEnum (EnumTypeInt 64))
      insConstraintEnv tDom tDom'
      return ((m, WeakTermArray dom' k), (m, WeakTermTau))
    (m, WeakTermArrayIntro k es) -> do
      tCod <- inferKind m k
      (es', ts) <- unzip <$> mapM (infer' ctx) es
      forM_ (zip ts (repeat tCod)) $ uncurry insConstraintEnv
      let len = toInteger $ length es
      let dom = (m, WeakTermInt (i64 m) len)
      -- let dom = (m, WeakTermEnumIntro (EnumValueInt 64 len))
      let t = (m, WeakTermArray dom k)
      return ((m, WeakTermArrayIntro k es'), t)
    (m, WeakTermArrayElim k xts e1 e2) -> do
      (e1', t1) <- infer' ctx e1
      (xts', (e2', t2)) <- inferBinder ctx xts e2
      let len = toInteger $ length xts
      let dom = (m, WeakTermInt (i64 m) len)
      -- let dom = (m, WeakTermEnumIntro (EnumValueInt 64 len))
      insConstraintEnv t1 (fst e1', WeakTermArray dom k)
      let ts = map (\(_, _, t) -> t) xts'
      tCod <- inferKind m k
      forM_ (zip ts (repeat tCod)) $ uncurry insConstraintEnv
      return ((m, WeakTermArrayElim k xts' e1' e2'), t2)
    (m, WeakTermStruct ts) ->
      return ((m, WeakTermStruct ts), (m, WeakTermTau))
    (m, WeakTermStructIntro eks) -> do
      let (es, ks) = unzip eks
      ts <- mapM (inferKind m) ks
      let structType = (m, WeakTermStruct ks)
      (es', ts') <- unzip <$> mapM (infer' ctx) es
      forM_ (zip ts' ts) $ uncurry insConstraintEnv
      return ((m, WeakTermStructIntro $ zip es' ks), structType)
    (m, WeakTermStructElim xks e1 e2) -> do
      (e1', t1) <- infer' ctx e1
      let (ms, xs, ks) = unzip3 xks
      ts <- mapM (inferKind m) ks
      let structType = (fst e1', WeakTermStruct ks)
      insConstraintEnv t1 structType
      forM_ (zip xs ts) $ uncurry insWeakTypeEnv
      (e2', t2) <- infer' (ctx ++ zip3 ms xs ts) e2
      return ((m, WeakTermStructElim xks e1' e2'), t2)
    (m, WeakTermCase mIndName e cxtes) -> do
      (e', t') <- infer' ctx e
      resultType <- newTypeHoleInCtx ctx m
      if null cxtes
        then return ((m, WeakTermCase mIndName e' []), resultType) -- ex falso quodlibet
        else do
          (indName, indInfo) <- getIndInfo $ map (fst . fst) cxtes
          (indType, argHoleList) <- constructIndType m ctx indName
          -- indType = a @ (HOLE, ..., HOLE)
          insConstraintEnv indType t'
          cxtes' <-
            forM (zip indInfo cxtes) $ \(is, (((mc, c), args), body)) -> do
              let usedHoleList = map (argHoleList !!) is
              args' <- inferPatArgs ctx args
              let items = map (\(mx, x, tx) -> ((mx, WeakTermUpsilon x), tx)) args'
              et <- infer' ctx (mc, WeakTermUpsilon c)
              -- et <- infer' ctx (mc, WeakTermConst c)
              _ <- inferPiElim ctx m et (usedHoleList ++ items)
              (body', bodyType) <- infer' (ctx ++ args') body
              insConstraintEnv resultType bodyType
              xts <- mapM (toWeakIdentPlus mc) usedHoleList
              return (((mc, c), xts ++ args'), body')
          return ((m, WeakTermCase (Just indName) e' cxtes'), resultType)
    (m, WeakTermQuestion e _) -> do
      (e', te) <- infer' ctx e
      return ((m, WeakTermQuestion e' te), te)
    (_, WeakTermErase _ e) ->
      infer' ctx e

toWeakIdentPlus :: Meta -> (WeakTermPlus, WeakTermPlus) -> WithEnv WeakIdentPlus
toWeakIdentPlus m (_, t) = do
  x <- newNameWith' "pat"
  return (m, x, t)

inferArgs ::
  Meta ->
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

constructIndType ::
  Meta ->
  Context ->
  Ident ->
  WithEnv (WeakTermPlus, [(WeakTermPlus, WeakTermPlus)])
constructIndType m ctx x = do
  senv <- gets substEnv
  case IntMap.lookup (asInt x) senv of
    Just e ->
      case e of
        e'@(me, WeakTermPiIntro Nothing xts cod) -> do
          holeList <- mapM (const $ newHoleInCtx ctx me) xts
          _ <- inferArgs m holeList xts cod
          let es = map (\(h, _) -> h) holeList
          return ((me, WeakTermPiElim e' es), holeList)
        e' ->
          raiseCritical m $
            "the definition of inductive type must be of the form `(lambda (xts) (...))`, but is:\n"
              <> toText e'
    _ -> raiseCritical m $ "no such inductive type defined: " <> asText x

getIndInfo :: [(Meta, Ident)] -> WithEnv (Ident, [[Int]])
getIndInfo cs = do
  (indNameList, usedPosList) <- unzip <$> mapM getIndInfo' cs
  checkIntegrity indNameList
  return (snd $ head indNameList, usedPosList)

getIndInfo' :: (Meta, Ident) -> WithEnv ((Meta, Ident), [Int])
getIndInfo' (m, c) = do
  rienv <- gets revIndEnv
  case Map.lookup (asText c) rienv of
    Just (i, is) ->
      return ((m, i), is)
    _ ->
      raiseError m $ "no such constructor defined: " <> asText c

checkIntegrity :: [(Meta, Ident)] -> WithEnv ()
checkIntegrity mis =
  case mis of
    [] ->
      return ()
    (mi : is) ->
      checkIntegrity' mi is

checkIntegrity' :: (Meta, Ident) -> [(Meta, Ident)] -> WithEnv ()
checkIntegrity' i mjs =
  case mjs of
    [] ->
      return ()
    (j : js) ->
      if snd i == snd j
        then checkIntegrity' i js
        else raiseError (supMeta (fst i) (fst j)) "foo"

inferPatArgs :: Context -> [WeakIdentPlus] -> WithEnv [WeakIdentPlus]
inferPatArgs ctx args =
  case args of
    [] ->
      return []
    ((mx, x, t) : xts) -> do
      t' <- inferType' ctx t
      insWeakTypeEnv x t'
      xts' <- inferPatArgs (ctx ++ [(mx, x, t')]) xts
      return $ (mx, x, t') : xts'

inferExternal :: Meta -> T.Text -> WithEnv TermPlus -> WithEnv (WeakTermPlus, WeakTermPlus)
inferExternal m x comp = do
  t <- comp
  return ((m, WeakTermConst x), (m, snd $ weaken t))

inferType' :: Context -> WeakTermPlus -> WithEnv WeakTermPlus
inferType' ctx t = do
  (t', u) <- infer' ctx t
  insConstraintEnv u (metaOf t, WeakTermTau)
  return t'

inferKind :: Meta -> ArrayKind -> WithEnv WeakTermPlus
inferKind m kind =
  case kind of
    ArrayKindInt size ->
      return (m, WeakTermConst (showIntSize size))
    ArrayKindFloat size ->
      return (m, WeakTermConst (showFloatSize size))
    _ ->
      raiseCritical m "inferKind for void-pointer"

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

inferSigma :: Context -> [WeakIdentPlus] -> WithEnv [WeakIdentPlus]
inferSigma ctx binder =
  case binder of
    [] ->
      return []
    ((mx, x, t) : xts) -> do
      t' <- inferType' ctx t
      insWeakTypeEnv x t'
      xts' <- inferSigma (ctx ++ [(mx, x, t')]) xts
      return $ (mx, x, t') : xts'

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
  Meta ->
  (WeakTermPlus, WeakTermPlus) ->
  [(WeakTermPlus, WeakTermPlus)] ->
  WithEnv (WeakTermPlus, WeakTermPlus)
inferPiElim ctx m (e, t) ets = do
  let es = map fst ets
  case t of
    (_, WeakTermPi _ xts cod)
      | length xts == length ets -> do
        cod' <- inferArgs m ets xts cod
        return ((m, WeakTermPiElim e es), cod')
    _ -> do
      ys <- mapM (const $ newNameWith' "arg") es
      yts <- newTypeHoleListInCtx ctx $ zip ys (map metaOf es)
      cod <- newTypeHoleInCtx (ctx ++ yts) m
      insConstraintEnv t (metaOf e, weakTermPi yts cod)
      cod' <- inferArgs m ets yts cod
      return ((m, WeakTermPiElim e es), cod')

-- In a context (x1 : A1, ..., xn : An), this function creates metavariables
--   ?M  : Pi (x1 : A1, ..., xn : An). ?Mt @ (x1, ..., xn)
--   ?Mt : Pi (x1 : A1, ..., xn : An). Univ
-- and return ?M @ (x1, ..., xn) : ?Mt @ (x1, ..., xn).
-- Note that we can't just set `?M : Pi (x1 : A1, ..., xn : An). Univ` since
-- WeakTermHole might be used as an ordinary term, that is, a term which is not a type.
newHoleInCtx :: Context -> Meta -> WithEnv (WeakTermPlus, WeakTermPlus)
newHoleInCtx ctx m = do
  higherHole <- newHole m
  let varSeq = map (\(_, x, _) -> (m, WeakTermUpsilon x)) ctx
  let higherApp = (m, WeakTermPiElim higherHole varSeq)
  hole <- newHole m
  let app = (m, WeakTermPiElim hole varSeq)
  return (app, higherApp)

-- In a context (x1 : A1, ..., xn : An), this function creates a metavariable
--   ?M  : Pi (x1 : A1, ..., xn : An). Univ{i}
-- and return ?M @ (x1, ..., xn) : Univ{i}.
newTypeHoleInCtx :: Context -> Meta -> WithEnv WeakTermPlus
newTypeHoleInCtx ctx m = do
  let varSeq = map (\(_, x, _) -> (m, WeakTermUpsilon x)) ctx
  hole <- newHole m
  return (m, WeakTermPiElim hole varSeq)

-- In context ctx == [x1, ..., xn], `newTypeHoleListInCtx ctx [y1, ..., ym]` generates
-- the following list:
--
--   [(y1,   ?M1   @ (x1, ..., xn)),
--    (y2,   ?M2   @ (x1, ..., xn, y1),
--    ...,
--    (y{m}, ?M{m} @ (x1, ..., xn, y1, ..., y{m-1}))]
--
-- inserting type information `yi : ?Mi @ (x1, ..., xn, y1, ..., y{i-1})
newTypeHoleListInCtx :: Context -> [(Ident, Meta)] -> WithEnv [WeakIdentPlus]
newTypeHoleListInCtx ctx ids =
  case ids of
    [] ->
      return []
    ((x, m) : rest) -> do
      t <- newTypeHoleInCtx ctx m
      insWeakTypeEnv x t
      ts <- newTypeHoleListInCtx (ctx ++ [(m, x, t)]) rest
      return $ (m, x, t) : ts

inferEnumCase :: Context -> EnumCasePlus -> WithEnv (EnumCasePlus, WeakTermPlus)
inferEnumCase ctx weakCase =
  case weakCase of
    (m, EnumCaseLabel name) -> do
      k <- lookupKind m name
      return (weakCase, (m, WeakTermEnum k))
    (m, EnumCaseDefault) -> do
      h <- newTypeHoleInCtx ctx m
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

lookupWeakTypeEnv :: Meta -> Ident -> WithEnv WeakTermPlus
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

lookupKind :: Meta -> T.Text -> WithEnv T.Text
lookupKind m name = do
  renv <- gets revEnumEnv
  case Map.lookup name renv of
    Nothing ->
      raiseError m $ "no such enum-intro is defined: " <> name
    Just (j, _) ->
      return j

insertImplicits :: WeakTermPlus -> [WeakTermPlus] -> WithEnv [WeakTermPlus]
insertImplicits e es =
  case e of
    (m, WeakTermUpsilon x)
      | not (metaIsExplicit m) ->
        insertImplicits' m x es
    _ ->
      return es

insertImplicits' :: Meta -> Ident -> [WeakTermPlus] -> WithEnv [WeakTermPlus]
insertImplicits' m x es = do
  ienv <- gets impEnv
  case IntMap.lookup (asInt x) ienv of
    Nothing ->
      return es
    Just is ->
      supplyHole m is 0 es

supplyHole :: Meta -> [Int] -> Int -> [WeakTermPlus] -> WithEnv [WeakTermPlus]
supplyHole m is idx es =
  if idx `elem` is
    then do
      h <- newHole m
      es' <- supplyHole m is (idx + 1) es
      return $ h : es'
    else case es of
      [] ->
        return []
      headTerm : rest -> do
        rest' <- supplyHole m is (idx + 1) rest
        return $ headTerm : rest'
