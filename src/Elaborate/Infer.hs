{-# LANGUAGE OverloadedStrings #-}

module Elaborate.Infer
  ( infer
  , inferType
  , inferSigma
  , insLevelEQ
  , insLevelLE
  , insConstraintEnv
  , univInstWith
  , instantiate
  , insWeakTypeEnv
  ) where

import Control.Monad.Except
import Control.Monad.State

-- import Data.Maybe (maybeToList)
import qualified Data.HashMap.Strict as Map
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Set as S
import qualified Data.Text as T

import Data.Basic
import Data.Env
import Data.Term hiding (IdentifierPlus)
import Data.WeakTerm

type Context = [IdentifierPlus]

-- type Context = [(IdentifierPlus, UnivLevelPlus)]
-- type Context = [(Identifier, WeakTermPlus)]
-- Given a term and a context, return the type of the term, updating the
-- constraint environment. This is more or less the same process in ordinary
-- Hindley-Milner type inference algorithm. The difference is that, when we
-- create a type variable, the type variable may depend on terms.
-- For example, consider generating constraints from an application `e1 @ e2`.
-- In ordinary predicate logic, we generate a type variable `?M` and add a
-- constraint `<type-of-e1> == <type-of-e2> -> ?M`. In dependent situation, however,
-- we cannot take this approach, since the `?M` may depend on other terms defined
-- beforehand. If `?M` depends on other terms, we cannot define substitution for terms
-- that contain metavariables because we don't know whether a substitution {x := e}
-- affects the content of a metavariable.
-- To handle this situation, we define metavariables to be *closed*. To represent
-- dependence, we apply all the names defined beforehand to the metavariables.
-- In other words, when we generate a metavariable, we use `?M @ (x1, ..., xn)` as a
-- representation of the hole, where x1, ..., xn are the defined names, or the context.
-- With this design, we can handle dependence in a simple way. This design decision
-- is due to "Elaboration in Dependent Type Theory". There also exists an approach
-- that deals with this situation which uses so-called contextual modality.
-- Interested readers are referred to A. Abel and B. Pientka. "Higher-Order
-- Dynamic Pattern Unification for Dependent Types and Records". Typed Lambda
-- Calculi and Applications, 2011.
infer :: WeakTermPlus -> WithEnv (WeakTermPlus, WeakTermPlus, UnivLevelPlus)
infer e = infer' [] e

inferType :: WeakTermPlus -> WithEnv (WeakTermPlus, UnivLevelPlus)
inferType t = inferType' [] t

infer' ::
     Context
  -> WeakTermPlus
  -> WithEnv (WeakTermPlus, WeakTermPlus, UnivLevelPlus)
infer' _ (m, WeakTermTau _) = do
  ml0 <- newLevelLT m []
  ml1 <- newLevelLT m [ml0]
  ml2 <- newLevelLT m [ml1]
  return (asUniv ml0, asUniv ml1, ml2)
infer' _ (m, WeakTermUpsilon x) = inferSymbol m x
infer' ctx (m, WeakTermPi mName xts t) = do
  (xtls', (t', mlPiCod)) <- inferPi ctx xts t
  let (xts', mlPiArgs) = unzip xtls'
  ml0 <- newLevelLE m $ mlPiCod : mlPiArgs
  ml1 <- newLevelLT m [ml0]
  return ((m, WeakTermPi mName xts' t'), (asUniv ml0), ml1)
infer' ctx (m, WeakTermPiIntro xts e) = do
  (xtls', (e', t', mlPiCod)) <- inferBinder ctx xts e
  let (xts', mlPiArgs) = unzip xtls'
  mlPi <- newLevelLE m $ mlPiCod : mlPiArgs
  return ((m, WeakTermPiIntro xts' e'), (m, weakTermPi xts' t'), mlPi)
infer' ctx (m, WeakTermPiIntroNoReduce xts e) = do
  (xtls', (e', t', mlPiCod)) <- inferBinder ctx xts e
  let (xts', mlPiArgs) = unzip xtls'
  mlPi <- newLevelLE m $ mlPiCod : mlPiArgs
  return ((m, WeakTermPiIntroNoReduce xts' e'), (m, weakTermPi xts' t'), mlPi)
infer' ctx (m, WeakTermPiIntroPlus ind (name, args1, args2) xts e) = do
  let args = args1 ++ args2
  (args', _) <- unzip <$> inferSigma ctx args
  let args1' = take (length args1) args'
  let args2' = drop (length args1) args'
  (xtls', (e', t', mlPiCod)) <- inferBinder ctx xts e
  let (xts', mlPiArgs) = unzip xtls'
  mlPi <- newLevelLE m $ mlPiCod : mlPiArgs
  return
    ( (m, WeakTermPiIntroPlus ind (name, args1', args2') xts' e')
    , (m, WeakTermPi (Just ind) xts' t') -- fixme: lookup indName
    , mlPi)
infer' ctx (m, WeakTermPiElim e es) = do
  es' <- insertHoleIfNecessary e es
  etls <- mapM (infer' ctx) es'
  etl <- infer' ctx e
  inferPiElim ctx m etl etls
infer' ctx (m, WeakTermIter (mx, x, t) xts e) = do
  tl'@(t', ml') <- inferType' ctx t
  insWeakTypeEnv x tl'
  -- Note that we cannot extend context with x. The type of e cannot be dependent on `x`.
  -- Otherwise the type of `mu x. e` might have `x` as free variable, which is unsound.
  (xtls', (e', tCod, mlPiCod)) <- inferBinder ctx xts e
  let (xts', mlPiArgs) = unzip xtls'
  mlPi <- newLevelLE m $ mlPiCod : mlPiArgs
  let piType = (m, weakTermPi xts' tCod)
  insConstraintEnv piType t'
  insLevelEQ mlPi ml'
  return ((m, WeakTermIter (mx, x, t') xts' e'), piType, mlPi)
infer' ctx (m, WeakTermZeta x) = do
  zenv <- gets zetaEnv
  case IntMap.lookup (asInt x) zenv of
    Just hole -> return hole
    Nothing -> do
      (app, higherApp, ml) <- newHoleInCtx ctx m
      modify
        (\env ->
           env {zetaEnv = IntMap.insert (asInt x) (app, higherApp, ml) zenv})
      return (app, higherApp, ml)
infer' _ (m, WeakTermConst x@(I (s, _)) _)
  -- i64, f16, u8, etc.
  | Just _ <- asLowTypeMaybe s = do
    ml0 <- newLevelLE m []
    ml1 <- newLevelLT m [ml0]
    -- i64とかf16とかは定義に展開されないのでunivParamsをもつ必要がない、はず
    return ((m, WeakTermConst x emptyUP), (asUniv ml0), ml1)
  | Just op <- asUnaryOpMaybe s = inferExternal m x (unaryOpToType m op)
  | Just op <- asBinaryOpMaybe s = inferExternal m x (binaryOpToType m op)
  | Just lt <- asArrayAccessMaybe s = inferExternal m x (arrayAccessToType m lt)
  | otherwise = inferSymbol m x
infer' _ (m, WeakTermInt t i) = do
  (t', UnivLevelPlus (_, l)) <- inferType' [] t -- ctx == [] since t' should be i64, i8, etc. (i.e. t must be closed)
  return ((m, WeakTermInt t' i), t', UnivLevelPlus (m, l))
infer' _ (m, WeakTermFloat16 f) = do
  ml <- newLevelLE m []
  (_, f16) <- lookupConstantPlus m "f16"
  return ((m, WeakTermFloat16 f), (m, f16), ml)
infer' _ (m, WeakTermFloat32 f) = do
  ml <- newLevelLE m []
  (_, f32) <- lookupConstantPlus m "f32"
  return ((m, WeakTermFloat32 f), (m, f32), ml)
infer' _ (m, WeakTermFloat64 f) = do
  ml <- newLevelLE m []
  (_, f64) <- lookupConstantPlus m "f64"
  return ((m, WeakTermFloat64 f), (m, f64), ml)
infer' _ (m, WeakTermFloat t f) = do
  (t', UnivLevelPlus (_, l)) <- inferType' [] t -- t must be closed
  return ((m, WeakTermFloat t' f), t', UnivLevelPlus (m, l))
infer' _ (m, WeakTermEnum name) = do
  ml0 <- newLevelLE m []
  ml1 <- newLevelLT m [ml0]
  return ((m, WeakTermEnum name), asUniv ml0, ml1)
infer' _ (m, WeakTermEnumIntro v) = do
  ml <- newLevelLE m []
  case v of
    EnumValueIntS size _ -> do
      let t = (m, WeakTermEnum (EnumTypeIntS size))
      return ((m, WeakTermEnumIntro v), t, ml)
    EnumValueIntU size _ -> do
      let t = (m, WeakTermEnum (EnumTypeIntU size))
      return ((m, WeakTermEnumIntro v), t, ml)
    EnumValueLabel l -> do
      k <- lookupKind m l
      let t = (m, WeakTermEnum $ EnumTypeLabel k)
      return ((m, WeakTermEnumIntro v), t, ml)
infer' ctx (m, WeakTermEnumElim (e, t) ces) = do
  (tEnum, mlEnum) <- inferType' ctx t
  (e', t', ml') <- infer' ctx e
  insConstraintEnv tEnum t'
  insLevelEQ mlEnum ml'
  if null ces
    then do
      h <- newTypeHoleInCtx ctx m
      ml <- newLevelLE m []
      return ((m, WeakTermEnumElim (e', t') []), h, ml) -- ex falso quodlibet
    else do
      let (cs, es) = unzip ces
      (cs', tcs) <- unzip <$> mapM (inferWeakCase ctx) cs
      forM_ (zip (repeat t') tcs) $ uncurry insConstraintEnv
      (es', ts, mls) <- unzip3 <$> mapM (infer' ctx) es
      constrainList $ ts
      constrainList $ map asUniv mls
      return ((m, WeakTermEnumElim (e', t') $ zip cs' es'), head ts, head mls)
infer' ctx (m, WeakTermArray dom k) = do
  (dom', tDom, mlDom) <- infer' ctx dom
  let tDom' = (m, WeakTermEnum (EnumTypeIntU 64))
  insConstraintEnv tDom tDom'
  ml0 <- newLevelLE m [mlDom]
  ml1 <- newLevelLT m [ml0]
  return ((m, WeakTermArray dom' k), asUniv ml0, ml1)
infer' ctx (m, WeakTermArrayIntro k es) = do
  tCod <- inferKind m k
  (es', ts, mls) <- unzip3 <$> mapM (infer' ctx) es
  forM_ (zip ts (repeat tCod)) $ uncurry insConstraintEnv
  constrainList $ map asUniv mls
  let len = toInteger $ length es
  let dom = (m, WeakTermEnumIntro (EnumValueIntU 64 len))
  let t = (m, WeakTermArray dom k)
  ml <- newLevelLE m mls
  return ((m, WeakTermArrayIntro k es'), t, ml)
infer' ctx (m, WeakTermArrayElim k xts e1 e2) = do
  (e1', t1, mlArr) <- infer' ctx e1
  (xtls', (e2', t2, ml2)) <- inferBinder ctx xts e2
  let (xts', mls) = unzip xtls'
  forM_ mls $ \mlArrArg -> insLevelLE mlArrArg mlArr
  let len = toInteger $ length xts
  let dom = (m, WeakTermEnumIntro (EnumValueIntU 64 len))
  insConstraintEnv t1 (fst e1', WeakTermArray dom k)
  let ts = map (\(_, _, t) -> t) xts'
  tCod <- inferKind m k
  forM_ (zip ts (repeat tCod)) $ uncurry insConstraintEnv
  return ((m, WeakTermArrayElim k xts' e1' e2'), t2, ml2)
infer' _ (m, WeakTermStruct ts) = do
  ml0 <- newLevelLE m []
  ml1 <- newLevelLT m [ml0]
  return ((m, WeakTermStruct ts), asUniv ml0, ml1)
infer' ctx (m, WeakTermStructIntro eks) = do
  let (es, ks) = unzip eks
  ts <- mapM (inferKind m) ks
  let structType = (m, WeakTermStruct ks)
  (es', ts', mls) <- unzip3 <$> mapM (infer' ctx) es
  forM_ (zip ts' ts) $ uncurry insConstraintEnv
  ml <- newLevelLE m mls
  return ((m, WeakTermStructIntro $ zip es' ks), structType, ml)
infer' ctx (m, WeakTermStructElim xks e1 e2) = do
  (e1', t1, mlStruct) <- infer' ctx e1
  let (ms, xs, ks) = unzip3 xks
  ts <- mapM (inferKind m) ks
  ls <- mapM (const newCount) ts
  let mls = map UnivLevelPlus $ zip (repeat m) ls
  forM_ mls $ \mlStructArg -> insLevelLE mlStructArg mlStruct
  let structType = (fst e1', WeakTermStruct ks)
  insConstraintEnv t1 structType
  forM_ (zip xs (zip ts mls)) $ uncurry insWeakTypeEnv
  (e2', t2, ml2) <- infer' (ctx ++ zip3 ms xs ts) e2
  return ((m, WeakTermStructElim xks e1' e2'), t2, ml2)
infer' ctx (m, WeakTermCase (e, t) cxtes) = do
  (tInd, mlInd) <- inferType' ctx t
  (e', t', ml') <- infer' ctx e
  insConstraintEnv tInd t'
  insLevelEQ mlInd ml'
  if null cxtes
    then do
      h <- newTypeHoleInCtx ctx m
      ml <- newLevelLE m []
      return ((m, WeakTermCase (e', t') []), h, ml) -- ex falso quodlibet
    else do
      cxttes' <-
        forM cxtes $ \(((mc, c), xts), body) -> do
          xts' <- supplyImplicit mc c xts >>= inferPatArgs ctx
          -- fixme: inferSymbolからimplicitの議論を消したのでcaseのほうでも処理を更新する必要あり。
          (tc, l) <- inferPattern mc c xts'
          insConstraintEnv tc t'
          insLevelEQ l mlInd
          (body', bodyType, bodyLevel) <- infer' ctx body
          return ((((mc, c), xts'), body'), (bodyType, bodyLevel))
      let (cxtes', bodyTypeLevelList) = unzip cxttes'
      let (bodyTypeList, bodyLevelList) = unzip bodyTypeLevelList
      constrainList bodyTypeList
      constrainLevelList bodyLevelList
      return
        ( (m, WeakTermCase (e', t') cxtes')
        , head bodyTypeList
        , head bodyLevelList)

inferPattern ::
     Meta
  -> Identifier
  -> [IdentifierPlus]
  -> WithEnv (WeakTermPlus, UnivLevelPlus)
inferPattern m c xts = do
  (_, t, l) <- inferSymbol m c -- ここでctxを与えてるのがへん？
  case t of
    (_, WeakTermPi _ yts cod)
      | length xts == length yts -> do
        cod' <- inferPattern' xts yts cod
        return (cod', l)
    _ -> raiseError m "arity mismatch"

inferPattern' ::
     [IdentifierPlus]
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> WithEnv WeakTermPlus
inferPattern' [] [] cod = return cod
inferPattern' ((mx, x, tx):xts) ((my, y, ty):yts) cod = do
  insConstraintEnv tx ty
  let varX = (supMeta mx my, WeakTermUpsilon x)
  let (yts', cod') = substWeakTermPlus'' [(y, varX)] yts cod
  inferPattern' xts yts' cod'
inferPattern' _ _ _ =
  raiseCritical' "invalid argument(s) passed to Infer.inferPattern"

inferPatArgs :: Context -> [IdentifierPlus] -> WithEnv [IdentifierPlus]
inferPatArgs _ [] = return []
inferPatArgs ctx ((mx, x, t):xts) = do
  tl'@(t', _) <- inferType' ctx t
  insWeakTypeEnv x tl'
  modify (\env -> env {patVarEnv = S.insert (asInt x) (patVarEnv env)})
  xts' <- inferPatArgs (ctx ++ [(mx, x, t')]) xts
  return $ (mx, x, t') : xts'

insertHoleIfNecessary ::
     WeakTermPlus -> [WeakTermPlus] -> WithEnv [WeakTermPlus]
insertHoleIfNecessary (m, WeakTermUpsilon x) es
  | not (metaIsExplicit m) = insertHoleIfNecessary' m x es
insertHoleIfNecessary (m, WeakTermConst x _) es
  | not (metaIsExplicit m) = insertHoleIfNecessary' m x es
insertHoleIfNecessary _ es = return es

insertHoleIfNecessary' ::
     Meta -> Identifier -> [WeakTermPlus] -> WithEnv [WeakTermPlus]
insertHoleIfNecessary' m x es = do
  ienv <- gets impEnv
  case IntMap.lookup (asInt x) ienv of
    Nothing -> return es
    Just is -> do
      mt <- lookupTypeEnv x
      case mt of
        Nothing ->
          raiseCritical m $
          "the type of `" <>
          asText x <>
          "` is supposed to be a Pi-type, but its type is not even in the type environment"
        Just ((_, TermPi _ xts _), _) -> supplyHole' m 0 (length xts) is es
        Just (t, _) ->
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
  -> WithEnv (WeakTermPlus, WeakTermPlus, UnivLevelPlus)
inferExternal m x comp = do
  t <- comp
  l <- newCount
  (_, t', l') <- instantiate m t l
  return ((m, WeakTermConst x emptyUP), t', l')

inferSymbol ::
     Meta -> Identifier -> WithEnv (WeakTermPlus, WeakTermPlus, UnivLevelPlus)
inferSymbol m x = do
  mt <- lookupTypeEnv x
  case mt of
    Nothing -> do
      ((_, t), UnivLevelPlus (_, l)) <- lookupWeakTypeEnv m x
      return ((m, WeakTermUpsilon x), (m, t), UnivLevelPlus (m, l)) -- infer時点で型環境に登録されていない <=> xは変数
    Just (t, UnivLevelPlus (_, l)) -> do
      (up, t', l') <- instantiate m t l
      return ((m, WeakTermConst x up), t', l')

instantiate ::
     Meta
  -> TermPlus
  -> Int
  -> WithEnv (UnivParams, WeakTermPlus, UnivLevelPlus)
instantiate m t l = do
  (up, (_, t'), l') <- univInst (weaken t) l
  return (up, (m, t'), UnivLevelPlus (m, l'))

supplyImplicit ::
     Meta -> Identifier -> [IdentifierPlus] -> WithEnv [IdentifierPlus]
supplyImplicit m c xts = do
  ienv <- gets impEnv
  t <- lookupTypeEnv' m c
  case (t, IntMap.lookup (asInt c) ienv) of
    ((_, TermPi _ yts _), Just is) -> do
      let argLen = length yts
      supplyImplicit' m 0 argLen is xts
    (_, Nothing) -> return xts
    _ ->
      raiseCritical m $
      "the type of " <>
      asText' c <> " must be a pi-type, but is:\n" <> toText (weaken t)

supplyImplicit' ::
     Meta -> Int -> Int -> [Int] -> [IdentifierPlus] -> WithEnv [IdentifierPlus]
supplyImplicit' m idx len is xts
  | idx < len = do
    if idx `elem` is
      then do
        xts' <- supplyImplicit' m (idx + 1) len is xts
        h <- newNameWith' "pat"
        t <- newHole m
        return $ (m, h, t) : xts'
      else supplyImplicit' m (idx + 1) len is xts
  | otherwise = return xts

-- inferImplicit ::
--      Context
--   -> Meta
--   -> Identifier
--   -> [Int]
--   -> WithEnv (WeakTermPlus, WeakTermPlus, UnivLevelPlus)
-- inferImplicit ctx m x is = do
--   mt <- lookupTypeEnv x
--   case mt of
--     Nothing ->
--       raiseCritical m $
--       "the type of `" <>
--       asText x <>
--       "` is supposed to be an implicit type, but its type is not even in the type environment"
--     Just (t@(_, TermPi {}), UnivLevelPlus (_, l)) -> do
--       (up, (_, WeakTermPi _ xts cod), l') <- instantiate m t l -- irrefutable pat
--       let xtis = zip xts [0 ..]
--       -- let xtis = zip (zip xts mls) [0 ..]
--       let vs = map (\(_, y, _) -> (m, WeakTermUpsilon y)) xts
--       let app = (m, WeakTermPiElim (m, WeakTermConst x up) vs)
--       (xtis', e', cod') <- inferImplicit' ctx m is xtis app cod
--       p "xtis:"
--       p' xtis
--       p "xtis':"
--       p' xtis'
--       -- let mls' = map fst $ filter (\(_, k) -> k `notElem` is) $ zip mls [0 ..]
--       let piType = (m, weakTermPi xtis' cod')
--       return ((m, WeakTermPiIntro xtis' e'), piType, l')
--     Just (t, _) ->
--       raiseCritical m $
--       "the type of `" <>
--       asText x <> "` must be a Pi-type, but is:\n" <> toText (weaken t)
-- inferImplicit' ::
--      Context
--   -> Meta
--   -> [Int]
--   -> [(IdentifierPlus, Int)]
--   -> WeakTermPlus
--   -> WeakTermPlus
--   -> WithEnv ([IdentifierPlus], WeakTermPlus, WeakTermPlus)
-- inferImplicit' _ _ _ [] e cod = return ([], e, cod)
-- inferImplicit' ctx m is ((c@(_, x, t), i):xtis) e cod
--   | i `elem` is = do
--     (app, higherApp, _) <- newHoleInCtx ctx m
--     p "ins:"
--     p' (higherApp, t)
--     insConstraintEnv higherApp t
--     let (xts, ks) = unzip xtis
--     let (xts', e', cod') = substWeakTermPlus''' [(x, app)] xts e cod
--     inferImplicit' ctx m is (zip xts' ks) e' cod'
--   | otherwise = do
--     (xtis', e', cod') <- inferImplicit' (ctx ++ [c]) m is xtis e cod
--     return ((m, x, t) : xtis', e', cod')
inferType' :: Context -> WeakTermPlus -> WithEnv (WeakTermPlus, UnivLevelPlus)
inferType' ctx t = do
  (t', u, l) <- infer' ctx t
  ml <- newLevelLE (fst t') []
  insConstraintEnv u (asUniv ml)
  insLevelLT ml l
  return (t', ml)

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
  -> WithEnv ([(IdentifierPlus, UnivLevelPlus)], (WeakTermPlus, UnivLevelPlus))
inferPi ctx [] cod = do
  (cod', mlPiCod) <- inferType' ctx cod
  return ([], (cod', mlPiCod))
inferPi ctx ((mx, x, t):xts) cod = do
  tl'@(t', ml) <- inferType' ctx t
  insWeakTypeEnv x tl'
  (xtls', tlCod) <- inferPi (ctx ++ [(mx, x, t')]) xts cod
  return (((mx, x, t'), ml) : xtls', tlCod)

inferSigma ::
     Context -> [IdentifierPlus] -> WithEnv [(IdentifierPlus, UnivLevelPlus)]
inferSigma _ [] = return []
inferSigma ctx ((mx, x, t):xts) = do
  tl'@(t', ml) <- inferType' ctx t
  insWeakTypeEnv x tl'
  xts' <- inferSigma (ctx ++ [(mx, x, t')]) xts
  return $ ((mx, x, t'), ml) : xts'

inferBinder ::
     Context
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> WithEnv ( [(IdentifierPlus, UnivLevelPlus)]
             , (WeakTermPlus, WeakTermPlus, UnivLevelPlus))
inferBinder ctx [] e = do
  etl' <- infer' ctx e
  return ([], etl')
inferBinder ctx ((mx, x, t):xts) e = do
  tl'@(t', ml) <- inferType' ctx t
  insWeakTypeEnv x tl'
  -- (xtls', etl') <- inferBinder (ctx ++ [((mx, x, t'), ml)]) xts e
  (xtls', etl') <- inferBinder (ctx ++ [(mx, x, t')]) xts e
  return (((mx, x, t'), ml) : xtls', etl')

inferPiElim ::
     Context
  -> Meta
  -> (WeakTermPlus, WeakTermPlus, UnivLevelPlus)
  -> [(WeakTermPlus, WeakTermPlus, UnivLevelPlus)]
  -> WithEnv (WeakTermPlus, WeakTermPlus, UnivLevelPlus)
inferPiElim ctx m (e, t, mlPi) etls = do
  let (es, ts, mlPiDomList) = unzip3 etls
  ys <- mapM (const $ newNameWith' "arg") es
  yts <- newTypeHoleListInCtx ctx $ zip ys (map fst es)
  let ts'' = map (\(_, _, ty) -> substWeakTermPlus (zip ys es) ty) yts
  cod <- newTypeHoleInCtx (ctx ++ yts) m
  insConstraintEnv t (fst e, weakTermPi yts cod)
  forM_ (zip ts ts'') $ uncurry insConstraintEnv
  forM_ mlPiDomList $ \ml -> insLevelLE ml mlPi
  mlPiCod <- newLevelLE m []
  insLevelLE mlPiCod mlPi
  return ((m, WeakTermPiElim e es), substWeakTermPlus (zip ys es) cod, mlPiCod)

-- In a context (x1 : A1, ..., xn : An), this function creates metavariables
--   ?M  : Pi (x1 : A1, ..., xn : An). ?Mt @ (x1, ..., xn)
--   ?Mt : Pi (x1 : A1, ..., xn : An). Univ
-- and return ?M @ (x1, ..., xn) : ?Mt @ (x1, ..., xn).
-- Note that we can't just set `?M : Pi (x1 : A1, ..., xn : An). Univ` since
-- WeakTermZeta might be used as an ordinary term, that is, a term which is not a type.
-- {} newHoleInCtx {}
newHoleInCtx ::
     Context -> Meta -> WithEnv (WeakTermPlus, WeakTermPlus, UnivLevelPlus)
newHoleInCtx ctx m = do
  higherHole <- newHole m
  let varSeq = map (\(_, x, _) -> (m, WeakTermUpsilon x)) ctx
  let higherApp = (m, WeakTermPiElim higherHole varSeq)
  hole <- newHole m
  let app = (m, WeakTermPiElim hole varSeq)
  ml <- newLevelLE m []
  return (app, higherApp, ml)

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
  ml <- newLevelLE m []
  insWeakTypeEnv x (t, ml)
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
  (t', _) <- inferType' ctx t
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

constrainLevelList :: [UnivLevelPlus] -> WithEnv ()
constrainLevelList [] = return ()
constrainLevelList [_] = return ()
constrainLevelList (l1:l2:ls) = do
  insLevelEQ l1 l2
  constrainLevelList $ l2 : ls

insConstraintEnv :: WeakTermPlus -> WeakTermPlus -> WithEnv ()
insConstraintEnv t1 t2 =
  modify (\e -> e {constraintEnv = (t1, t2) : constraintEnv e})

insWeakTypeEnv :: Identifier -> (WeakTermPlus, UnivLevelPlus) -> WithEnv ()
insWeakTypeEnv (I (_, i)) tl =
  modify (\e -> e {weakTypeEnv = IntMap.insert i tl (weakTypeEnv e)})

lookupWeakTypeEnv :: Meta -> Identifier -> WithEnv (WeakTermPlus, UnivLevelPlus)
lookupWeakTypeEnv m s = do
  mt <- lookupWeakTypeEnvMaybe s
  case mt of
    Just t -> return t
    Nothing ->
      raiseCritical m $
      asText' s <> " is not found in the weak type environment."

lookupWeakTypeEnvMaybe ::
     Identifier -> WithEnv (Maybe (WeakTermPlus, UnivLevelPlus))
lookupWeakTypeEnvMaybe (I (_, s)) = do
  mt <- gets (IntMap.lookup s . weakTypeEnv)
  case mt of
    Nothing -> return Nothing
    Just t -> return $ Just t

lookupKind :: Meta -> T.Text -> WithEnv T.Text
lookupKind m name = do
  renv <- gets revEnumEnv
  case Map.lookup name renv of
    Nothing -> raiseError m $ "no such enum-intro is defined: " <> name
    Just (j, _) -> return j

newLevelLE :: Meta -> [UnivLevelPlus] -> WithEnv UnivLevelPlus
newLevelLE m mls = do
  l <- newCount
  let ml = UnivLevelPlus (m, l)
  forM_ mls $ \ml' -> insLevelLE ml' ml
  return ml

newLevelLT :: Meta -> [UnivLevelPlus] -> WithEnv UnivLevelPlus
newLevelLT m mls = do
  l <- newCount
  let ml = UnivLevelPlus (m, l)
  forM_ mls $ \ml' -> insLevelLT ml' ml
  return ml

insLevelLE :: UnivLevelPlus -> UnivLevelPlus -> WithEnv ()
insLevelLE ml1 ml2 =
  modify (\env -> env {levelEnv = (ml1, (0, ml2)) : levelEnv env})

insLevelLT :: UnivLevelPlus -> UnivLevelPlus -> WithEnv ()
insLevelLT ml1 ml2 =
  modify (\env -> env {levelEnv = (ml1, (1, ml2)) : levelEnv env})

insLevelEQ :: UnivLevelPlus -> UnivLevelPlus -> WithEnv ()
insLevelEQ (UnivLevelPlus (_, l1)) (UnivLevelPlus (_, l2)) = do
  modify (\env -> env {equalityEnv = (l1, l2) : equalityEnv env})

univInst ::
     WeakTermPlus -> UnivLevel -> WithEnv (UnivParams, WeakTermPlus, UnivLevel)
univInst e l = do
  modify (\env -> env {univRenameEnv = IntMap.empty})
  e' <- univInst' e
  l' <- levelInst l
  up <- gets univRenameEnv
  return (up, e', l')

univInstWith :: IntMap.IntMap UnivLevel -> WeakTermPlus -> WithEnv WeakTermPlus
univInstWith univParams e = do
  modify (\env -> env {univRenameEnv = univParams})
  univInst' e

univInst' :: WeakTermPlus -> WithEnv WeakTermPlus
univInst' (m, WeakTermTau l) = do
  l' <- levelInst l
  return (m, WeakTermTau l')
univInst' (m, WeakTermUpsilon x) = return (m, WeakTermUpsilon x)
univInst' (m, WeakTermPi mName xts t) = do
  xts' <- univInstArgs xts
  t' <- univInst' t
  return (m, WeakTermPi mName xts' t')
univInst' (m, WeakTermPiIntro xts e) = do
  xts' <- univInstArgs xts
  e' <- univInst' e
  return (m, WeakTermPiIntro xts' e')
univInst' (m, WeakTermPiIntroNoReduce xts e) = do
  xts' <- univInstArgs xts
  e' <- univInst' e
  return (m, WeakTermPiIntroNoReduce xts' e')
univInst' (m, WeakTermPiIntroPlus ind (name, args1, args2) xts e) = do
  args1' <- univInstArgs args1
  args2' <- univInstArgs args2
  xts' <- univInstArgs xts
  e' <- univInst' e
  return (m, WeakTermPiIntroPlus ind (name, args1', args2') xts' e')
univInst' (m, WeakTermPiElim e es) = do
  e' <- univInst' e
  es' <- mapM univInst' es
  return (m, WeakTermPiElim e' es')
univInst' (m, WeakTermIter (mx, x, t) xts e) = do
  t' <- univInst' t
  xts' <- univInstArgs xts
  e' <- univInst' e
  return (m, WeakTermIter (mx, x, t') xts' e')
univInst' (m, WeakTermConst x up) = do
  up' <- mapM levelInst up
  return (m, WeakTermConst x up')
univInst' (m, WeakTermZeta x) = return (m, WeakTermZeta x)
univInst' (m, WeakTermInt t a) = do
  t' <- univInst' t
  return (m, WeakTermInt t' a)
univInst' (m, WeakTermFloat16 a) = return (m, WeakTermFloat16 a)
univInst' (m, WeakTermFloat32 a) = return (m, WeakTermFloat32 a)
univInst' (m, WeakTermFloat64 a) = return (m, WeakTermFloat64 a)
univInst' (m, WeakTermFloat t a) = do
  t' <- univInst' t
  return (m, WeakTermFloat t' a)
univInst' (m, WeakTermEnum x) = return (m, WeakTermEnum x)
univInst' (m, WeakTermEnumIntro l) = return (m, WeakTermEnumIntro l)
univInst' (m, WeakTermEnumElim (e, t) les) = do
  t' <- univInst' t
  e' <- univInst' e
  let (ls, es) = unzip les
  es' <- mapM univInst' es
  return (m, WeakTermEnumElim (e', t') (zip ls es'))
univInst' (m, WeakTermArray dom k) = do
  dom' <- univInst' dom
  return (m, WeakTermArray dom' k)
univInst' (m, WeakTermArrayIntro k es) = do
  es' <- mapM univInst' es
  return (m, WeakTermArrayIntro k es')
univInst' (m, WeakTermArrayElim k xts d e) = do
  xts' <- univInstArgs xts
  d' <- univInst' d
  e' <- univInst' e
  return (m, WeakTermArrayElim k xts' d' e')
univInst' (m, WeakTermStruct ks) = return (m, WeakTermStruct ks)
univInst' (m, WeakTermStructIntro ets) = do
  let (es, ks) = unzip ets
  es' <- mapM univInst' es
  return (m, WeakTermStructIntro (zip es' ks))
univInst' (m, WeakTermStructElim xts d e) = do
  d' <- univInst' d
  e' <- univInst' e
  return (m, WeakTermStructElim xts d' e')
univInst' (m, WeakTermCase (e, t) cxtes) = do
  e' <- univInst' e
  t' <- univInst' t
  cxtes' <-
    flip mapM cxtes $ \((c, xts), body) -> do
      xts' <- univInstArgs xts
      body' <- univInst' body
      return ((c, xts'), body')
  return (m, WeakTermCase (e', t') cxtes')

univInstArgs :: [IdentifierPlus] -> WithEnv [IdentifierPlus]
univInstArgs xts = do
  let (ms, xs, ts) = unzip3 xts
  ts' <- mapM univInst' ts
  return $ zip3 ms xs ts'

levelInst :: UnivLevel -> WithEnv UnivLevel
levelInst l = do
  urenv <- gets univRenameEnv
  case IntMap.lookup l urenv of
    Just l' -> return l'
    Nothing -> do
      l' <- newCount
      modify (\env -> env {univRenameEnv = IntMap.insert l l' urenv})
      uienv <- gets univInstEnv
      let s = S.fromList [l, l']
      modify (\env -> env {univInstEnv = IntMap.insertWith S.union l s uienv})
      return l'
