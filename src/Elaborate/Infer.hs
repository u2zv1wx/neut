{-# LANGUAGE OverloadedStrings #-}

module Elaborate.Infer
  ( infer
  , inferType
  , inferSigma
  , insConstraintEnv
  , insWeakTypeEnv
  , newTypeHoleInCtx
  , Context
  ) where

import Control.Monad.Except
import Control.Monad.State

import qualified Data.HashMap.Strict as Map
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Text as T

import Data.Basic
import Data.Env
import Data.Term hiding (IdentifierPlus)
import Data.WeakTerm

type Context = [IdentifierPlus]

infer :: WeakTermPlus -> WithEnv (WeakTermPlus, WeakTermPlus)
infer e = infer' [] e

inferType :: WeakTermPlus -> WithEnv WeakTermPlus
inferType t = inferType' [] t

infer' :: Context -> WeakTermPlus -> WithEnv (WeakTermPlus, WeakTermPlus)
infer' _ (m, WeakTermTau) = return ((m, WeakTermTau), (m, WeakTermTau))
infer' _ (m, WeakTermUpsilon x) = inferSymbol m x
infer' ctx (m, WeakTermPi mName xts t) = do
  (xts', t') <- inferPi ctx xts t
  return ((m, WeakTermPi mName xts' t'), (m, WeakTermTau))
infer' ctx (m, WeakTermPiIntro xts e) = do
  (xts', (e', t')) <- inferBinder ctx xts e
  return ((m, WeakTermPiIntro xts' e'), (m, weakTermPi xts' t'))
infer' ctx (m, WeakTermPiIntroPlus ind (name, is, args) xts e)
  -- let args = args1 ++ args2
 = do
  args' <- inferSigma ctx args
  -- let args1' = take (length args1) args'
  -- let args2' = drop (length args1) args'
  (xts', (e', t')) <- inferBinder ctx xts e
  return
    ( (m, WeakTermPiIntroPlus ind (name, is, args') xts' e')
    , (m, WeakTermPi (Just $ asText ind) xts' t'))
infer' ctx (m, WeakTermPiElim e es) = do
  es' <- insertHoleIfNecessary e es
  etls <- mapM (infer' ctx) es'
  etl <- infer' ctx e
  inferPiElim ctx m etl etls
infer' ctx (m, WeakTermIter (mx, x, t) xts e) = do
  t' <- inferType' ctx t
  insWeakTypeEnv x t'
  -- Note that we cannot extend context with x. The type of e cannot be dependent on `x`.
  -- Otherwise the type of `mu x. e` might have `x` as free variable, which is unsound.
  (xts', (e', tCod)) <- inferBinder ctx xts e
  let piType = (m, weakTermPi xts' tCod)
  insConstraintEnv piType t'
  return ((m, WeakTermIter (mx, x, t') xts' e'), piType)
infer' ctx (m, WeakTermZeta x) = do
  zenv <- gets zetaEnv
  case IntMap.lookup (asInt x) zenv of
    Just hole -> return hole
    Nothing -> do
      (app, higherApp) <- newHoleInCtx ctx m
      modify
        (\env -> env {zetaEnv = IntMap.insert (asInt x) (app, higherApp) zenv})
      return (app, higherApp)
infer' _ (m, WeakTermConst x@(I (s, _)))
  -- i64, f16, u8, etc.
  | Just _ <- asLowTypeMaybe s = return ((m, WeakTermConst x), (m, WeakTermTau))
  | Just op <- asUnaryOpMaybe s = inferExternal m x (unaryOpToType m op)
  | Just op <- asBinaryOpMaybe s = inferExternal m x (binaryOpToType m op)
  | Just lt <- asArrayAccessMaybe s = inferExternal m x (arrayAccessToType m lt)
  | otherwise = inferSymbol m x
infer' _ (m, WeakTermInt t i) = do
  t' <- inferType' [] t -- ctx == [] since t' should be i64, i8, etc. (i.e. t must be closed)
  return ((m, WeakTermInt t' i), t')
infer' _ (m, WeakTermFloat t f) = do
  t' <- inferType' [] t -- t must be closed
  return ((m, WeakTermFloat t' f), t')
infer' _ (m, WeakTermEnum name) =
  return ((m, WeakTermEnum name), (m, WeakTermTau))
infer' _ (m, WeakTermEnumIntro v) = do
  case v of
    EnumValueIntS size _ -> do
      let t = (m, WeakTermEnum (EnumTypeIntS size))
      return ((m, WeakTermEnumIntro v), t)
    EnumValueIntU size _ -> do
      let t = (m, WeakTermEnum (EnumTypeIntU size))
      return ((m, WeakTermEnumIntro v), t)
    EnumValueLabel l -> do
      k <- lookupKind m l
      let t = (m, WeakTermEnum $ EnumTypeLabel k)
      return ((m, WeakTermEnumIntro v), t)
infer' ctx (m, WeakTermEnumElim (e, t) ces) = do
  tEnum <- inferType' ctx t
  (e', t') <- infer' ctx e
  insConstraintEnv tEnum t'
  if null ces
    then do
      h <- newTypeHoleInCtx ctx m
      return ((m, WeakTermEnumElim (e', t') []), h) -- ex falso quodlibet
    else do
      let (cs, es) = unzip ces
      (cs', tcs) <- unzip <$> mapM (inferWeakCase ctx) cs
      forM_ (zip (repeat t') tcs) $ uncurry insConstraintEnv
      (es', ts) <- unzip <$> mapM (infer' ctx) es
      constrainList $ ts
      return ((m, WeakTermEnumElim (e', t') $ zip cs' es'), head ts)
infer' ctx (m, WeakTermArray dom k) = do
  (dom', tDom) <- infer' ctx dom
  let tDom' = (m, WeakTermEnum (EnumTypeIntU 64))
  insConstraintEnv tDom tDom'
  return ((m, WeakTermArray dom' k), (m, WeakTermTau))
infer' ctx (m, WeakTermArrayIntro k es) = do
  tCod <- inferKind m k
  (es', ts) <- unzip <$> mapM (infer' ctx) es
  forM_ (zip ts (repeat tCod)) $ uncurry insConstraintEnv
  let len = toInteger $ length es
  let dom = (m, WeakTermEnumIntro (EnumValueIntU 64 len))
  let t = (m, WeakTermArray dom k)
  return ((m, WeakTermArrayIntro k es'), t)
infer' ctx (m, WeakTermArrayElim k xts e1 e2) = do
  (e1', t1) <- infer' ctx e1
  (xts', (e2', t2)) <- inferBinder ctx xts e2
  let len = toInteger $ length xts
  let dom = (m, WeakTermEnumIntro (EnumValueIntU 64 len))
  insConstraintEnv t1 (fst e1', WeakTermArray dom k)
  let ts = map (\(_, _, t) -> t) xts'
  tCod <- inferKind m k
  forM_ (zip ts (repeat tCod)) $ uncurry insConstraintEnv
  return ((m, WeakTermArrayElim k xts' e1' e2'), t2)
infer' _ (m, WeakTermStruct ts) =
  return ((m, WeakTermStruct ts), (m, WeakTermTau))
infer' ctx (m, WeakTermStructIntro eks) = do
  let (es, ks) = unzip eks
  ts <- mapM (inferKind m) ks
  let structType = (m, WeakTermStruct ks)
  (es', ts') <- unzip <$> mapM (infer' ctx) es
  forM_ (zip ts' ts) $ uncurry insConstraintEnv
  return ((m, WeakTermStructIntro $ zip es' ks), structType)
infer' ctx (m, WeakTermStructElim xks e1 e2) = do
  (e1', t1) <- infer' ctx e1
  let (ms, xs, ks) = unzip3 xks
  ts <- mapM (inferKind m) ks
  let structType = (fst e1', WeakTermStruct ks)
  insConstraintEnv t1 structType
  forM_ (zip xs ts) $ uncurry insWeakTypeEnv
  (e2', t2) <- infer' (ctx ++ zip3 ms xs ts) e2
  return ((m, WeakTermStructElim xks e1' e2'), t2)
infer' ctx (m, WeakTermCase indName e cxtes) = do
  (e', t') <- infer' ctx e
  resultType <- newTypeHoleInCtx ctx m
  if null cxtes
    then do
      return ((m, WeakTermCase indName e' []), resultType) -- ex falso quodlibet
    else do
      (name@(I (nameStr, _)), indInfo) <- getIndInfo $ map (fst . fst) cxtes
      (indType, argHoleList) <- constructIndType m ctx name
      -- indType = a @ (HOLE, ..., HOLE)
      insConstraintEnv indType t'
      cxtes' <-
        forM (zip indInfo cxtes) $ \(is, (((mc, c), patArgs), body)) -> do
          let usedHoleList = map (\i -> argHoleList !! i) is
          let var = (mc, WeakTermUpsilon c)
          patArgs' <- inferPatArgs ctx patArgs
          let items =
                map (\(mx, x, tx) -> ((mx, WeakTermUpsilon x), tx)) patArgs'
          etl <- infer' ctx var
          _ <- inferPiElim ctx m etl (usedHoleList ++ items)
          (body', bodyType) <- infer' (ctx ++ patArgs') body
          insConstraintEnv resultType bodyType
          xts <- mapM (toIdentPlus mc) usedHoleList
          return (((mc, c), xts ++ patArgs'), body')
      return ((m, WeakTermCase nameStr e' cxtes'), resultType)
infer' ctx (m, WeakTermQuestion e _) = do
  (e', te) <- infer' ctx e
  return ((m, WeakTermQuestion e' te), te)
infer' ctx (_, WeakTermErase _ e) = infer' ctx e

toIdentPlus :: Meta -> (WeakTermPlus, WeakTermPlus) -> WithEnv IdentifierPlus
toIdentPlus m (_, t) = do
  x <- newNameWith' "pat"
  return (m, x, t)

inferArgs ::
     Meta
  -> [(WeakTermPlus, WeakTermPlus)]
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> WithEnv WeakTermPlus
inferArgs _ [] [] cod = return cod
inferArgs m ((e, t):ets) ((_, x, tx):xts) cod = do
  insConstraintEnv t tx
  let (xts', cod') = substWeakTermPlus'' [(x, e)] xts cod
  inferArgs m ets xts' cod'
inferArgs m _ _ _ = raiseCritical m $ "invalid argument passed to inferArgs"

constructIndType ::
     Meta
  -> Context
  -> Identifier
  -> WithEnv (WeakTermPlus, [(WeakTermPlus, WeakTermPlus)])
constructIndType m ctx i = do
  cenv <- gets cacheEnv
  case IntMap.lookup (asInt i) cenv of
    Just (Left e) -> do
      case weaken e of
        e'@(me, WeakTermPiIntro xts cod) -> do
          holeList <- mapM (const $ newHoleInCtx ctx me) xts
          _ <- inferArgs m holeList xts cod
          let es = map (\(h, _) -> h) holeList
          return ((me, WeakTermPiElim e' es), holeList)
        e' ->
          raiseCritical m $
          "the definition of inductive type must be of the form `(lambda (xts) (...))`, but is:\n" <>
          toText e'
    _ -> raiseCritical m $ "no such inductive type defined: " <> asText i

getIndInfo :: [(Meta, Identifier)] -> WithEnv (Identifier, [[Int]])
getIndInfo cs = do
  (indNameList, usedPosList) <- unzip <$> mapM getIndInfo' cs
  checkIntegrity indNameList
  return (snd $ head indNameList, usedPosList)

getIndInfo' :: (Meta, Identifier) -> WithEnv ((Meta, Identifier), [Int])
getIndInfo' (m, c) = do
  cienv <- gets consToIndInfo
  case Map.lookup (asText c) cienv of
    Just (i, is) -> return ((m, i), is)
    _ -> raiseError m $ "no such constructor defined: " <> asText c

checkIntegrity :: [(Meta, Identifier)] -> WithEnv ()
checkIntegrity [] = return ()
checkIntegrity (mi:is) = checkIntegrity' mi is

checkIntegrity' :: (Meta, Identifier) -> [(Meta, Identifier)] -> WithEnv ()
checkIntegrity' _ [] = return ()
checkIntegrity' i (j:js) =
  if snd i == snd j
    then checkIntegrity' i js
    else raiseError (supMeta (fst i) (fst j)) "foo"

inferPatArgs :: Context -> [IdentifierPlus] -> WithEnv [IdentifierPlus]
inferPatArgs _ [] = return []
inferPatArgs ctx ((mx, x, t):xts) = do
  t' <- inferType' ctx t
  insWeakTypeEnv x t'
  xts' <- inferPatArgs (ctx ++ [(mx, x, t')]) xts
  return $ (mx, x, t') : xts'

insertHoleIfNecessary ::
     WeakTermPlus -> [WeakTermPlus] -> WithEnv [WeakTermPlus]
insertHoleIfNecessary (m, WeakTermUpsilon x) es
  | not (metaIsExplicit m) = insertHoleIfNecessary' m x es
insertHoleIfNecessary (m, WeakTermConst x) es
  | not (metaIsExplicit m) = insertHoleIfNecessary' m x es
insertHoleIfNecessary _ es = return es

insertHoleIfNecessary' ::
     Meta -> Identifier -> [WeakTermPlus] -> WithEnv [WeakTermPlus]
insertHoleIfNecessary' m x es = do
  ienv <- gets impEnv
  case IntMap.lookup (asInt x) ienv of
    Nothing -> return es
    Just is -> do
      tl <- lookupTypeEnv m x
      case tl of
        (_, TermPi _ xts _) -> supplyHole' m 0 (length xts) is es
        t ->
          raiseCritical m $
          "the type of `" <>
          asText x <> "` must be a Pi-type, but is:\n" <> toText (weaken t)

supplyHole' ::
     Meta -> Int -> Int -> [Int] -> [WeakTermPlus] -> WithEnv [WeakTermPlus]
supplyHole' m idx len is es
  | idx < len = do
    if idx `elem` is
      then do
        xts' <- supplyHole' m (idx + 1) len is es
        h <- newHole m
        return $ h : xts'
      else supplyHole' m (idx + 1) len is es
  | otherwise = return es

inferExternal ::
     Meta
  -> Identifier
  -> WithEnv TermPlus
  -> WithEnv (WeakTermPlus, WeakTermPlus)
inferExternal m x comp = do
  t <- comp
  return ((m, WeakTermConst x), (m, snd $ weaken t))

inferSymbol :: Meta -> Identifier -> WithEnv (WeakTermPlus, WeakTermPlus)
inferSymbol m x = do
  mt <- lookupTypeEnvMaybe x
  case mt of
    Just t -> return ((m, WeakTermConst x), (m, snd $ weaken t))
    Nothing -> do
      (_, t) <- lookupWeakTypeEnv m x
      return ((m, WeakTermUpsilon x), (m, t))

inferType' :: Context -> WeakTermPlus -> WithEnv WeakTermPlus
inferType' ctx t = do
  (t', u) <- infer' ctx t
  insConstraintEnv u (metaOf t, WeakTermTau)
  return t'

inferKind :: Meta -> ArrayKind -> WithEnv WeakTermPlus
inferKind m (ArrayKindIntS i) = return (m, WeakTermEnum (EnumTypeIntS i))
inferKind m (ArrayKindIntU i) = return (m, WeakTermEnum (EnumTypeIntU i))
inferKind m (ArrayKindFloat size) = do
  (_, t) <- lookupConstantPlus m $ "f" <> T.pack (show (sizeAsInt size))
  return (m, t)
inferKind m _ = raiseCritical m "inferKind for void-pointer"

inferPi ::
     Context
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> WithEnv ([IdentifierPlus], WeakTermPlus)
inferPi ctx [] cod = do
  (cod', mlPiCod) <- inferType' ctx cod
  return ([], (cod', mlPiCod))
inferPi ctx ((mx, x, t):xts) cod = do
  t' <- inferType' ctx t
  insWeakTypeEnv x t'
  (xtls', tlCod) <- inferPi (ctx ++ [(mx, x, t')]) xts cod
  return ((mx, x, t') : xtls', tlCod)

inferSigma :: Context -> [IdentifierPlus] -> WithEnv [IdentifierPlus]
inferSigma _ [] = return []
inferSigma ctx ((mx, x, t):xts) = do
  t' <- inferType' ctx t
  insWeakTypeEnv x t'
  xts' <- inferSigma (ctx ++ [(mx, x, t')]) xts
  return $ (mx, x, t') : xts'

inferBinder ::
     Context
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> WithEnv ([IdentifierPlus], (WeakTermPlus, WeakTermPlus))
inferBinder ctx [] e = do
  etl' <- infer' ctx e
  return ([], etl')
inferBinder ctx ((mx, x, t):xts) e = do
  t' <- inferType' ctx t
  insWeakTypeEnv x t'
  (xts', etl') <- inferBinder (ctx ++ [(mx, x, t')]) xts e
  return ((mx, x, t') : xts', etl')

inferPiElim ::
     Context
  -> Meta
  -> (WeakTermPlus, WeakTermPlus)
  -> [(WeakTermPlus, WeakTermPlus)]
  -> WithEnv (WeakTermPlus, WeakTermPlus)
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
-- WeakTermZeta might be used as an ordinary term, that is, a term which is not a type.
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
newTypeHoleListInCtx ::
     Context -> [(Identifier, Meta)] -> WithEnv [IdentifierPlus]
newTypeHoleListInCtx _ [] = return []
newTypeHoleListInCtx ctx ((x, m):rest) = do
  t <- newTypeHoleInCtx ctx m
  insWeakTypeEnv x t
  ts <- newTypeHoleListInCtx (ctx ++ [(m, x, t)]) rest
  return $ (m, x, t) : ts

inferWeakCase :: Context -> WeakCasePlus -> WithEnv (WeakCasePlus, WeakTermPlus)
inferWeakCase _ l@(m, WeakCaseLabel name) = do
  k <- lookupKind m name
  return (l, (m, WeakTermEnum $ EnumTypeLabel k))
inferWeakCase _ l@(m, WeakCaseIntS size _) =
  return (l, (m, WeakTermEnum (EnumTypeIntS size)))
inferWeakCase _ l@(m, WeakCaseIntU size _) =
  return (l, (m, WeakTermEnum (EnumTypeIntU size)))
inferWeakCase ctx (m, WeakCaseInt t a) = do
  t' <- inferType' ctx t
  return ((m, WeakCaseInt t' a), t')
inferWeakCase ctx (m, WeakCaseDefault) = do
  h <- newTypeHoleInCtx ctx m
  return ((m, WeakCaseDefault), h)

constrainList :: [WeakTermPlus] -> WithEnv ()
constrainList [] = return ()
constrainList [_] = return ()
constrainList (t1:t2:ts) = do
  insConstraintEnv t1 t2
  constrainList $ t2 : ts

insConstraintEnv :: WeakTermPlus -> WeakTermPlus -> WithEnv ()
insConstraintEnv t1 t2 =
  modify (\e -> e {constraintEnv = (t1, t2) : constraintEnv e})

insWeakTypeEnv :: Identifier -> WeakTermPlus -> WithEnv ()
insWeakTypeEnv (I (_, i)) t =
  modify (\e -> e {weakTypeEnv = IntMap.insert i t (weakTypeEnv e)})

lookupWeakTypeEnv :: Meta -> Identifier -> WithEnv WeakTermPlus
lookupWeakTypeEnv m s = do
  mt <- lookupWeakTypeEnvMaybe s
  case mt of
    Just t -> return t
    Nothing ->
      raiseCritical m $
      asText' s <> " is not found in the weak type environment."

lookupWeakTypeEnvMaybe :: Identifier -> WithEnv (Maybe WeakTermPlus)
lookupWeakTypeEnvMaybe (I (_, s)) = do
  wtenv <- gets weakTypeEnv
  -- mt <- gets (IntMap.lookup s . weakTypeEnv)
  case IntMap.lookup s wtenv of
    Nothing -> return Nothing
    Just t -> return $ Just t

lookupKind :: Meta -> T.Text -> WithEnv T.Text
lookupKind m name = do
  renv <- gets revEnumEnv
  case Map.lookup name renv of
    Nothing -> raiseError m $ "no such enum-intro is defined: " <> name
    Just (j, _) -> return j
