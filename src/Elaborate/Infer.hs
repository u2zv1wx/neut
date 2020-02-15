{-# LANGUAGE OverloadedStrings #-}

module Elaborate.Infer
  ( infer
  , inferType
  , insLevelEQ
  , insConstraintEnv
  , termInst
  ) where

import Control.Monad.Except
import Control.Monad.State

import qualified Data.HashMap.Strict as Map
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Set as S
import qualified Data.Text as T

import Data.Basic
import Data.Env
import Data.Term hiding (IdentifierPlus)
import Data.WeakTerm

type Context = [(IdentifierPlus, UnivLevelPlus)]

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
-- {termはrename済みでclosed} infer' {termはrename済みでclosedで、かつすべてのsubtermが型でannotateされている}
-- infer :: WeakTermPlus -> WithEnv WeakTermPlus
-- infer e = do
--   (e', _, _) <- infer' [] e
--   let vs = varWeakTermPlus e'
--   let info = toInfo "inferred term is not closed. freevars:" vs
--   return $ assertP info e' $ null vs
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
  -- p $ "inferred tau at " ++ showMeta m ++ ":"
  -- p' (ml0, ml1, ml2)
  return (asUniv ml0, asUniv ml1, ml2)
infer' _ (m, WeakTermUpsilon x) = do
  mt <- lookupTypeEnv x
  case mt of
    Nothing -> do
      ((_, t), UnivLevelPlus (_, l)) <- lookupWeakTypeEnv x
      return ((m, WeakTermUpsilon x), (m, t), UnivLevelPlus (m, l))
    Just (t, UnivLevelPlus (_, l)) -> do
      ((_, t'), l') <- univInst (weaken t) l
      -- p $ "instantiate:" ++ T.unpack x
      -- p "from:"
      -- -- p $ T.unpack (toText (weaken t))
      -- p' t
      -- p "to:"
      -- -- p $ T.unpack (toText a)
      -- p' a
      -- p $ "level: " ++ show l ++ " ~> " ++ show l'
      return ((m, WeakTermUpsilon x), (m, t'), UnivLevelPlus (m, l'))
infer' ctx (m, WeakTermPi _ xts t) = do
  mls <- piUnivLevelsfrom xts t
  (xtls', (t', mlPiCod)) <- inferPi ctx xts t
  let (xts', mlPiArgs) = unzip xtls'
  ml0 <- newLevelLE m $ mlPiCod : mlPiArgs
  ml1 <- newLevelLT m [ml0]
  forM_ (zip mls (mlPiArgs ++ [mlPiCod])) $ uncurry insLevelEQ
  return ((m, WeakTermPi mls xts' t'), (asUniv ml0), ml1)
infer' ctx (m, WeakTermPiIntro xts e) = do
  (xtls', (e', t', mlPiCod)) <- inferBinder ctx xts e
  let (xts', mlPiArgs) = unzip xtls'
  mlPi <- newLevelLE m $ mlPiCod : mlPiArgs
  let mls = mlPiArgs ++ [mlPiCod]
  return ((m, WeakTermPiIntro xts' e'), (m, WeakTermPi mls xts' t'), mlPi)
infer' ctx (m, WeakTermPiElim (mPi, WeakTermPiIntro xts e) es) -- "let"
  | length xts == length es = do
    etls <- mapM (infer' ctx) es
    let (ms, xs, ts) = unzip3 xts
    tls' <- mapM (inferType' ctx) ts -- don't extend the context
    forM_ (zip xs tls') $ uncurry insWeakTypeEnv
    -- ctxをextendしなくてもdefListにそれ相当の情報がある
    (e', tCod, ml) <- infer' ctx e -- don't extend the context
    let (ts', mls) = unzip tls'
    mlPi <- newLevelLE m $ ml : mls
    let xts' = zip3 ms xs ts'
    let etl =
          ( (m, WeakTermPiIntro xts' e')
          , (mPi, WeakTermPi (mls ++ [ml]) xts' tCod)
          , mlPi)
    let (es', _, _) = unzip3 etls
    let defList = Map.fromList $ zip xs es'
    modify (\env -> env {substEnv = defList `Map.union` substEnv env})
    inferPiElim ctx m etl etls
infer' ctx (m, WeakTermPiElim e es) = do
  etls <- mapM (infer' ctx) es
  etl <- infer' ctx e
  inferPiElim ctx m etl etls
infer' ctx (m, WeakTermSigma xts) = do
  (xts', mls) <- unzip <$> inferSigma ctx xts
  ml0 <- newLevelLE m $ mls
  ml1 <- newLevelLT m [ml0]
  return ((m, WeakTermSigma xts'), (asUniv ml0), ml1)
infer' ctx (m, WeakTermSigmaIntro t es) = do
  (t', mlSigma) <- inferType' ctx t
  (es', ts, mlSigmaArgList) <- unzip3 <$> mapM (infer' ctx) es
  ys <- mapM (const $ newNameWith "arg") es'
  -- yts = [(y1, ?M1 @ (ctx[0], ..., ctx[n])),
  --        (y2, ?M2 @ (ctx[0], ..., ctx[n], y1)),
  --        ...,
  --        (ym, ?Mm @ (ctx[0], ..., ctx[n], y1, ..., y{m-1}))]
  ytls <- newTypeHoleListInCtx ctx $ zip ys (map fst es')
  let (yts, mls') = unzip ytls
  forM_ mlSigmaArgList $ \mlSigmaArg -> insLevelLE mlSigmaArg mlSigma
  -- ts' = [?M1 @ (ctx[0], ..., ctx[n]),
  --        ?M2 @ (ctx[0], ..., ctx[n], e1),
  --        ...,
  --        ?Mm @ (ctx[0], ..., ctx[n], e1, ..., e{m-1})]
  let ts' = map (\(_, _, ty) -> substWeakTermPlus (zip ys es) ty) yts
  let sigmaType = (m, WeakTermSigma yts)
  forM_ ((sigmaType, t') : zip ts ts') $ uncurry insConstraintEnv
  forM_ (zip mlSigmaArgList mls') $ uncurry insLevelEQ
  -- 中身をsigmaTypeにすることでelaborateのときに確実に中身を取り出せるようにする
  return ((m, WeakTermSigmaIntro sigmaType es'), sigmaType, mlSigma)
infer' ctx (m, WeakTermSigmaElim t xts e1 e2) = do
  (t', mlResult) <- inferType' ctx t
  (e1', t1, mlSigma) <- infer' ctx e1
  xtls <- inferSigma ctx xts
  let (xts', mlSigArgList) = unzip xtls
  (e2', t2, ml2) <- infer' (ctx ++ xtls) e2
  -- insert constraints
  insConstraintEnv t1 (fst e1', WeakTermSigma xts')
  forM_ mlSigArgList $ \mlSigArg -> insLevelLE mlSigArg mlSigma
  insConstraintEnv t2 t'
  insLevelEQ mlResult ml2
  return ((m, WeakTermSigmaElim t' xts' e1' e2'), t2, ml2)
infer' ctx (m, WeakTermIter (mx, x, t) xts e) = do
  tl'@(t', ml') <- inferType' ctx t
  insWeakTypeEnv x tl'
  -- Note that we cannot extend context with x. The type of e cannot be dependent on `x`.
  -- Otherwise the type of `mu x. e` might have `x` as free variable, which is unsound.
  (xtls', (e', tCod, mlPiCod)) <- inferBinder ctx xts e
  let (xts', mlPiArgs) = unzip xtls'
  mlPi <- newLevelLE m $ mlPiCod : mlPiArgs
  let piType = (m, WeakTermPi (mlPiArgs ++ [mlPiCod]) xts' tCod)
  insConstraintEnv piType t'
  insLevelEQ mlPi ml'
  return ((m, WeakTermIter (mx, x, t') xts' e'), piType, mlPi)
infer' ctx (m, WeakTermZeta x) = do
  (app, higherApp, ml) <- newHoleInCtx ctx m
  zenv <- gets zetaEnv
  case Map.lookup x zenv of
    Just (app', higherApp', ml') -> do
      insConstraintEnv app app'
      insConstraintEnv higherApp higherApp'
      insLevelEQ ml ml'
      return (app, higherApp, ml)
    Nothing -> do
      modify (\env -> env {zetaEnv = Map.insert x (app, higherApp, ml) zenv})
      return (app, higherApp, ml)
infer' _ (m, WeakTermConst x)
  -- i64, f16, u8, etc.
  | Just _ <- asLowTypeMaybe x = do
    ml0 <- newLevelLE m []
    ml1 <- newLevelLT m [ml0]
    return ((m, WeakTermConst x), (asUniv ml0), ml1)
  | otherwise = do
    mt <- lookupTypeEnv x
    case mt of
      Nothing -> do
        (t, UnivLevelPlus (_, l)) <- lookupWeakTypeEnv x
        return ((m, WeakTermConst x), t, UnivLevelPlus (m, l))
      Just (t, UnivLevelPlus (_, l)) -> do
        ((_, t'), l') <- univInst (weaken t) l
        return ((m, WeakTermConst x), (m, t'), UnivLevelPlus (m, l'))
infer' ctx (m, WeakTermConstDecl (mx, x, t) e) = do
  tl'@(t', _) <- inferType' ctx t
  insWeakTypeEnv x tl'
  -- the type of `e` doesn't depend on `x`
  (e', t'', ml) <- infer' ctx e
  return ((m, WeakTermConstDecl (mx, x, t') e'), t'', ml)
infer' _ (m, WeakTermInt t i) = do
  (t', UnivLevelPlus (_, l)) <- inferType' [] t -- ctx == [] since t' should be i64, i8, etc. (i.e. t must be closed)
  return ((m, WeakTermInt t' i), t', UnivLevelPlus (m, l))
infer' _ (m, WeakTermFloat16 f) = do
  ml <- newLevelLE m []
  return ((m, WeakTermFloat16 f), (m, WeakTermConst "f16"), ml)
infer' _ (m, WeakTermFloat32 f) = do
  ml <- newLevelLE m []
  return ((m, WeakTermFloat32 f), (m, WeakTermConst "f32"), ml)
infer' _ (m, WeakTermFloat64 f) = do
  ml <- newLevelLE m []
  return ((m, WeakTermFloat64 f), (m, WeakTermConst "f64"), ml)
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
    EnumValueNat i _ -> do
      let t = (m, WeakTermEnum $ EnumTypeNat i)
      return ((m, WeakTermEnumIntro v), t, ml)
    EnumValueLabel l -> do
      k <- lookupKind l
      let t = (m, WeakTermEnum $ EnumTypeLabel k)
      return ((m, WeakTermEnumIntro v), t, ml)
infer' ctx (m, WeakTermEnumElim (e, t) ces) = do
  (tEnum, mlEnum) <- inferType' ctx t
  (e', t', ml') <- infer' ctx e
  insConstraintEnv tEnum t'
  insLevelEQ mlEnum ml'
  if null ces
    then do
      (h, ml) <- newTypeHoleInCtx ctx m
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
  (dom', mlDom) <- inferType' ctx dom
  ml0 <- newLevelLE m [mlDom]
  ml1 <- newLevelLT m [ml0]
  return ((m, WeakTermArray dom' k), asUniv ml0, ml1)
infer' ctx (m, WeakTermArrayIntro k es) = do
  let tCod = inferKind k
  (es', ts, mls) <- unzip3 <$> mapM (infer' ctx) es
  forM_ (zip ts (repeat tCod)) $ uncurry insConstraintEnv
  constrainList $ map asUniv mls
  let len = toInteger $ length es
  let dom = (emptyMeta, WeakTermEnum (EnumTypeNat len))
  let t = (m, WeakTermArray dom k)
  ml <- newLevelLE m mls
  return ((m, WeakTermArrayIntro k es'), t, ml)
infer' ctx (m, WeakTermArrayElim k xts e1 e2) = do
  (e1', t1, mlArr) <- infer' ctx e1
  (xtls', (e2', t2, ml2)) <- inferBinder ctx xts e2
  let (xts', mls) = unzip xtls'
  forM_ mls $ \mlArrArg -> insLevelLE mlArrArg mlArr
  let dom = (emptyMeta, WeakTermEnum (EnumTypeNat (toInteger $ length xts)))
  insConstraintEnv t1 (fst e1', WeakTermArray dom k)
  let ts = map (\(_, _, t) -> t) xts'
  forM_ (zip ts (repeat (inferKind k))) $ uncurry insConstraintEnv
  return ((m, WeakTermArrayElim k xts' e1' e2'), t2, ml2)
infer' _ (m, WeakTermStruct ts) = do
  ml0 <- newLevelLE m []
  ml1 <- newLevelLT m [ml0]
  return ((m, WeakTermStruct ts), asUniv ml0, ml1)
infer' ctx (m, WeakTermStructIntro eks) = do
  let (es, ks) = unzip eks
  let ts = map inferKind ks
  let structType = (m, WeakTermStruct ks)
  (es', ts', mls) <- unzip3 <$> mapM (infer' ctx) es
  forM_ (zip ts' ts) $ uncurry insConstraintEnv
  ml <- newLevelLE m mls
  return ((m, WeakTermStructIntro $ zip es' ks), structType, ml)
infer' ctx (m, WeakTermStructElim xks e1 e2) = do
  (e1', t1, mlStruct) <- infer' ctx e1
  let (ms, xs, ks) = unzip3 xks
  let ts = map inferKind ks
  ls <- mapM (const newUnivLevel) ts
  let mls = map UnivLevelPlus $ zip (repeat m) ls
  forM_ mls $ \mlStructArg -> insLevelLE mlStructArg mlStruct
  let structType = (fst e1', WeakTermStruct ks)
  insConstraintEnv t1 structType
  forM_ (zip xs (zip ts mls)) $ uncurry insWeakTypeEnv
  (e2', t2, ml2) <- infer' (ctx ++ zip (zip3 ms xs ts) mls) e2
  return ((m, WeakTermStructElim xks e1' e2'), t2, ml2)

inferType' :: Context -> WeakTermPlus -> WithEnv (WeakTermPlus, UnivLevelPlus)
inferType' ctx t = do
  (t', u, l) <- infer' ctx t
  ml <- newLevelLE (fst t') []
  insConstraintEnv u (asUniv ml)
  insLevelLT ml l
  return (t', ml)

inferKind :: ArrayKind -> WeakTermPlus
inferKind (ArrayKindIntS i) = (emptyMeta, WeakTermEnum (EnumTypeIntS i))
inferKind (ArrayKindIntU i) = (emptyMeta, WeakTermEnum (EnumTypeIntU i))
inferKind (ArrayKindFloat size) =
  (emptyMeta, WeakTermConst $ "f" <> T.pack (show (sizeAsInt size)))
inferKind _ = error "inferKind for void-pointer"

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
  (xtls', tlCod) <- inferPi (ctx ++ [((mx, x, t'), ml)]) xts cod
  return (((mx, x, t'), ml) : xtls', tlCod)

inferSigma ::
     Context -> [IdentifierPlus] -> WithEnv [(IdentifierPlus, UnivLevelPlus)]
inferSigma _ [] = return []
inferSigma ctx ((mx, x, t):xts) = do
  tl'@(t', ml) <- inferType' ctx t
  insWeakTypeEnv x tl'
  xts' <- inferSigma (ctx ++ [((mx, x, t'), ml)]) xts
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
  (xtls', etl') <- inferBinder (ctx ++ [((mx, x, t'), ml)]) xts e
  return (((mx, x, t'), ml) : xtls', etl')

inferPiElim ::
     Context
  -> Meta
  -> (WeakTermPlus, WeakTermPlus, UnivLevelPlus)
  -> [(WeakTermPlus, WeakTermPlus, UnivLevelPlus)]
  -> WithEnv (WeakTermPlus, WeakTermPlus, UnivLevelPlus)
inferPiElim ctx m (e, t, mlPi) etls = do
  let (es, ts, mlPiDomList) = unzip3 etls
  case t of
    (_, WeakTermPi mls xts cod) -- performance optimization (not necessary for correctness)
      | length xts == length etls -> do
        let mlPiDomList' = init mls
        let mlPiCod' = last mls
        let xs = map (\(_, x, _) -> x) xts
        let ts'' = map (\(_, _, tx) -> substWeakTermPlus (zip xs es) tx) xts
        forM_ (zip ts'' ts) $ uncurry insConstraintEnv
        forM_ (zip mlPiDomList mlPiDomList') $ uncurry insLevelEQ
        forM_ mlPiDomList $ \mlPiDom -> insLevelLE mlPiDom mlPi
        insLevelLE mlPiCod' mlPi
        let cod' = substWeakTermPlus (zip xs es) cod
        return ((m, WeakTermPiElim e es), cod', mlPiCod')
    _ -> do
      ys <- mapM (const $ newNameWith "arg") es
      -- yts = [(y1, ?M1 @ (ctx[0], ..., ctx[n])),
      --        (y2, ?M2 @ (ctx[0], ..., ctx[n], y1)),
      --        ...,
      --        (ym, ?Mm @ (ctx[0], ..., ctx[n], y1, ..., y{m-1}))]
      ytls <- newTypeHoleListInCtx ctx $ zip ys (map fst es)
      let (yts, mls') = unzip ytls
      -- ts'' = [?M1 @ (ctx[0], ..., ctx[n]),
      --         ?M2 @ (ctx[0], ..., ctx[n], e1),
      --         ...,
      --         ?Mm @ (ctx[0], ..., ctx[n], e1, ..., e{m-1})]
      let ts'' = map (\(_, _, ty) -> substWeakTermPlus (zip ys es) ty) yts
      (cod, mlPiCod) <- newTypeHoleInCtx (ctx ++ ytls) m
      let cod' = substWeakTermPlus (zip ys es) cod
      forM_ (zip ts ts'') $ uncurry insConstraintEnv
      forM_ (zip mlPiDomList mls') $ uncurry insLevelEQ
      forM_ mlPiDomList $ \mlPiDom -> insLevelLE mlPiDom mlPi
      insLevelLE mlPiCod mlPi
      insConstraintEnv t (fst e, WeakTermPi (mlPiDomList ++ [mlPiCod]) yts cod)
      return ((m, WeakTermPiElim e es), cod', mlPiCod)

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
  higherHole <- newHole
  let varSeq = map (\((_, x, _), _) -> toVar x) ctx
  let higherApp = (m, WeakTermPiElim higherHole varSeq)
  hole <- newHole
  let app = (m, WeakTermPiElim hole varSeq)
  l <- newUnivLevel
  return (app, higherApp, UnivLevelPlus (m, l))

-- In a context (x1 : A1, ..., xn : An), this function creates a metavariable
--   ?M  : Pi (x1 : A1, ..., xn : An). Univ{i}
-- and return ?M @ (x1, ..., xn) : Univ{i}.
newTypeHoleInCtx :: Context -> Meta -> WithEnv (WeakTermPlus, UnivLevelPlus)
newTypeHoleInCtx ctx m = do
  let varSeq = map (\((_, x, _), _) -> toVar x) ctx
  hole <- newHole
  l <- newUnivLevel
  return ((m, WeakTermPiElim hole varSeq), UnivLevelPlus (m, l))

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
     Context
  -> [(Identifier, Meta)]
  -> WithEnv [(IdentifierPlus, UnivLevelPlus)]
newTypeHoleListInCtx _ [] = return []
newTypeHoleListInCtx ctx ((x, m):rest) = do
  tl@(t, ml) <- newTypeHoleInCtx ctx m
  insWeakTypeEnv x tl
  ts <- newTypeHoleListInCtx (ctx ++ [((m, x, t), ml)]) rest
  return $ ((m, x, t), ml) : ts

-- caseにもmetaの情報がほしいか。それはたしかに？
inferWeakCase :: Context -> WeakCase -> WithEnv (WeakCase, WeakTermPlus)
inferWeakCase _ l@(WeakCaseLabel name) = do
  k <- lookupKind name
  return (l, (emptyMeta, WeakTermEnum $ EnumTypeLabel k))
inferWeakCase _ l@(WeakCaseNat i _) =
  return (l, (emptyMeta, WeakTermEnum $ EnumTypeNat i))
inferWeakCase _ l@(WeakCaseIntS size _) =
  return (l, (emptyMeta, WeakTermEnum (EnumTypeIntS size)))
inferWeakCase _ l@(WeakCaseIntU size _) =
  return (l, (emptyMeta, WeakTermEnum (EnumTypeIntU size)))
inferWeakCase ctx (WeakCaseInt t a) = do
  (t', _) <- inferType' ctx t
  return (WeakCaseInt t' a, t')
inferWeakCase ctx WeakCaseDefault = do
  (h, _) <- newTypeHoleInCtx ctx emptyMeta
  return (WeakCaseDefault, h)

constrainList :: [WeakTermPlus] -> WithEnv ()
constrainList [] = return ()
constrainList [_] = return ()
constrainList (t1:t2:ts) = do
  insConstraintEnv t1 t2
  constrainList $ t2 : ts

-- toIsEnumType :: Integer -> Meta -> WithEnv WeakTermPlus
-- toIsEnumType i m = do
--   return
--     ( m
--     , WeakTermPiElim
--         (emptyMeta, WeakTermConst "is-enum")
--         [(emptyMeta, WeakTermEnum $ EnumTypeNat i)])
newHole :: WithEnv WeakTermPlus
newHole = do
  h <- newNameWith "hole"
  return (emptyMeta, WeakTermZeta h)

insConstraintEnv :: WeakTermPlus -> WeakTermPlus -> WithEnv ()
insConstraintEnv t1 t2 =
  modify (\e -> e {constraintEnv = (t1, t2) : constraintEnv e})

insWeakTypeEnv :: Identifier -> (WeakTermPlus, UnivLevelPlus) -> WithEnv ()
insWeakTypeEnv i tl =
  modify (\e -> e {weakTypeEnv = Map.insert i tl (weakTypeEnv e)})

lookupWeakTypeEnv :: Identifier -> WithEnv (WeakTermPlus, UnivLevelPlus)
lookupWeakTypeEnv s = do
  mt <- lookupWeakTypeEnvMaybe s
  case mt of
    Just t -> return t
    Nothing -> throwError' $ s <> " is not found in the weak type environment."

lookupWeakTypeEnvMaybe ::
     Identifier -> WithEnv (Maybe (WeakTermPlus, UnivLevelPlus))
lookupWeakTypeEnvMaybe s = do
  mt <- gets (Map.lookup s . weakTypeEnv)
  case mt of
    Nothing -> return Nothing
    Just t -> return $ Just t

lookupKind :: Identifier -> WithEnv Identifier
lookupKind name = do
  renv <- gets revEnumEnv
  case Map.lookup name renv of
    Nothing -> throwError' $ "no such enum-intro is defined: " <> name
    Just (j, _) -> return j

newLevelLE :: Meta -> [UnivLevelPlus] -> WithEnv UnivLevelPlus
newLevelLE m mls = do
  l <- newUnivLevel
  let ml = UnivLevelPlus (m, l)
  forM_ mls $ \ml' -> insLevelLE ml' ml
  return ml

newLevelLT :: Meta -> [UnivLevelPlus] -> WithEnv UnivLevelPlus
newLevelLT m mls = do
  l <- newUnivLevel
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

univInst :: WeakTermPlus -> UnivLevel -> WithEnv (WeakTermPlus, UnivLevel)
univInst e l = do
  modify (\env -> env {univRenameEnv = IntMap.empty})
  e' <- univInst' e
  l' <- levelInst l
  return (e', l')

termInst :: WeakTermPlus -> WithEnv WeakTermPlus
termInst e = do
  modify (\env -> env {univRenameEnv = IntMap.empty})
  univInst' e

univInst' :: WeakTermPlus -> WithEnv WeakTermPlus
univInst' (m, WeakTermTau l) = do
  l' <- levelInst l
  return (m, WeakTermTau l')
univInst' (m, WeakTermUpsilon x) = return (m, WeakTermUpsilon x)
univInst' (m, WeakTermPi mls xts t) = do
  xts' <- univInstArgs xts
  t' <- univInst' t
  let (ms, ls) = unzip $ map (\(UnivLevelPlus x) -> x) mls
  ls' <- mapM levelInst ls
  return (m, WeakTermPi (map UnivLevelPlus $ zip ms ls') xts' t')
univInst' (m, WeakTermPiIntro xts e) = do
  xts' <- univInstArgs xts
  e' <- univInst' e
  return (m, WeakTermPiIntro xts' e')
univInst' (m, WeakTermPiElim e es) = do
  e' <- univInst' e
  es' <- mapM univInst' es
  return (m, WeakTermPiElim e' es')
univInst' (m, WeakTermSigma xts) = do
  xts' <- univInstArgs xts
  return (m, WeakTermSigma xts')
univInst' (m, WeakTermSigmaIntro t es) = do
  t' <- univInst' t
  es' <- mapM univInst' es
  return (m, WeakTermSigmaIntro t' es')
univInst' (m, WeakTermSigmaElim t xts e1 e2) = do
  t' <- univInst' t
  xts' <- univInstArgs xts
  e1' <- univInst' e1
  e2' <- univInst' e2
  return (m, WeakTermSigmaElim t' xts' e1' e2')
univInst' (m, WeakTermIter (mx, x, t) xts e) = do
  t' <- univInst' t
  xts' <- univInstArgs xts
  e' <- univInst' e
  return (m, WeakTermIter (mx, x, t') xts' e')
univInst' (m, WeakTermConst x) = return (m, WeakTermConst x)
univInst' (m, WeakTermConstDecl (mx, x, t) e) = do
  t' <- univInst' t
  e' <- univInst' e
  return (m, WeakTermConstDecl (mx, x, t') e')
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
      l' <- newUnivLevel
      modify (\env -> env {univRenameEnv = IntMap.insert l l' urenv})
      uienv <- gets univInstEnv
      let s = S.fromList [l, l']
      modify (\env -> env {univInstEnv = IntMap.insertWith S.union l s uienv})
      return l'
