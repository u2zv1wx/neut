{-# LANGUAGE OverloadedStrings #-}

module Elaborate.Infer
  ( infer
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.Basic
import Data.Constraint
import Data.Env
import Data.WeakTerm

import qualified Data.HashMap.Strict as Map
import qualified Data.Text as T

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
infer :: WeakTermPlus -> WithEnv WeakTermPlus
infer e = do
  (e', _, _) <- infer' [] e
  let vs = varWeakTermPlus e'
  let info = toInfo "inferred term is not closed. freevars:" vs
  return $ assertP info e' $ null vs

infer' ::
     Context
  -> WeakTermPlus
  -> WithEnv (WeakTermPlus, WeakTermPlus, UnivLevelPlus)
infer' _ (m, WeakTermTau l0) = do
  let ml0 = UnivLevelPlus (m, l0)
  ml1 <- newLevelOver m [ml0]
  ml2 <- newLevelOver m [ml1]
  return (asUniv ml0, asUniv ml1, ml2)
infer' _ (m, WeakTermUpsilon x) = do
  ((_, t), (UnivLevelPlus (_, l))) <- lookupWeakTypeEnv x
  return ((m, WeakTermUpsilon x), (m, t), (UnivLevelPlus (m, l)))
infer' ctx (m, WeakTermPi xts t) = do
  (xtls', (t', ml)) <- inferPi ctx xts t
  let (xts', mls) = unzip xtls'
  ml0 <- newLevelOver m $ ml : mls
  ml1 <- newLevelOver m [ml0]
  return ((m, WeakTermPi xts' t'), (asUniv ml0), ml1)
infer' ctx (m, WeakTermPiIntro xts e) = do
  (xtls', (e', t', l)) <- inferBinder ctx xts e
  let (xts', ls) = unzip xtls'
  ml <- newLevelOver m $ l : ls
  -- let piType = (m, WeakTermPi xts' t')
  return ((m, WeakTermPiIntro xts' e'), (m, WeakTermPi xts' t'), ml)
  -- retWeakTerm piType m lu $ WeakTermPiIntro xts' e'
infer' ctx (m, WeakTermPiElim (mPi, WeakTermPiIntro xts e) es) -- "let"
  | length xts == length es = do
    etls <- mapM (infer' ctx) es
    let (ms, xs, ts) = unzip3 xts
    -- don't extend context
    tls' <- mapM (inferType ctx) ts
    let (ts', ls) = unzip tls'
    -- (ts', ls) <- unzip <$> mapM (inferType ctx) ts
    -- constrainList us
    forM_ (zip xs tls') $ uncurry insWeakTypeEnv
    -- forM_ xts' $ uncurry insWeakTypeEnv
    -- ctxをextendしなくてもdefListにそれ相当の情報がある
    (e', tCod, l) <- infer' ctx e -- don't extend context
    ml <- newLevelOver m $ l : ls
    let xts' = zip3 ms xs ts'
    let etl = ((m, WeakTermPiIntro xts' e'), (mPi, WeakTermPi xts' tCod), ml)
    let (es', _, _) = unzip3 etls
    let defList = Map.fromList $ zip xs es'
    modify (\env -> env {substEnv = defList `Map.union` substEnv env})
    inferPiElim ctx m etl etls
infer' ctx (m, WeakTermPiElim e es) = do
  etls <- mapM (infer' ctx) es
  etl <- infer' ctx e
  inferPiElim ctx m etl etls
infer' ctx (m, WeakTermSigma xts) = do
  (xts', ls) <- unzip <$> inferSigma ctx xts
  ml0 <- newLevelOver m $ ls
  ml1 <- newLevelOver m [ml0]
  return ((m, WeakTermSigma xts'), (asUniv ml0), ml1)
infer' ctx (m, WeakTermSigmaIntro t es) = do
  (t', ml) <- inferType ctx t
  (es', ts, mls) <- unzip3 <$> mapM (infer' ctx) es
  ys <- mapM (const $ newNameWith "arg") es'
  -- yts = [(y1, ?M1 @ (ctx[0], ..., ctx[n])),
  --        (y2, ?M2 @ (ctx[0], ..., ctx[n], y1)),
  --        ...,
  --        (ym, ?Mm @ (ctx[0], ..., ctx[n], y1, ..., y{m-1}))]
  ytls <- newTypeHoleListInCtx ctx $ zip ys (map fst es')
  let (yts, mls') = unzip ytls
  let sigmaType = (m, WeakTermSigma yts)
  forM_ (mls ++ mls') $ \ml' -> insLevelLT ml' ml
  let us1 = map asUniv mls
  let us2 = map asUniv mls'
  -- ts' = [?M1 @ (ctx[0], ..., ctx[n]),
  --        ?M2 @ (ctx[0], ..., ctx[n], e1),
  --        ...,
  --        ?Mm @ (ctx[0], ..., ctx[n], e1, ..., e{m-1})]
  let ts' = map (\(_, _, ty) -> substWeakTermPlus (zip ys es) ty) yts
  forM_ ((sigmaType, t') : zip ts ts') $ uncurry insConstraintEnv
  forM_ (zip us1 us2) $ uncurry insConstraintEnv
  -- retWeakTerm sigmaType m $ WeakTermSigmaIntro t' es'
  -- 中身をsigmaTypeにすることでelaborateのときに確実に中身を取り出せるようにする
  return ((m, WeakTermSigmaIntro sigmaType es'), sigmaType, ml)
  -- retWeakTerm sigmaType m undefined $ WeakTermSigmaIntro sigmaType es'
infer' ctx (m, WeakTermSigmaElim t xts e1 e2) = do
  (t', ml) <- inferType ctx t
  (e1', t1, mlSig) <- infer' ctx e1
  xtls <- inferSigma ctx xts
  let (xts', mlSigArgList) = unzip xtls
  forM_ mlSigArgList $ \mlSigArg -> insLevelLT mlSigArg mlSig
  let sigmaType = (fst e1', WeakTermSigma xts')
  insConstraintEnv t1 sigmaType
  (e2', t2, ml2) <- infer' (ctx ++ xtls) e2
  insConstraintEnv t2 t'
  insConstraintEnv (asUniv ml) (asUniv ml2)
  return ((m, WeakTermSigmaElim t' xts' e1' e2'), t2, ml2)
  -- retWeakTerm t2 m undefined $ WeakTermSigmaElim t' xts' e1' e2'
infer' ctx (m, WeakTermIter (mx, x, t) xts e) = do
  tl'@(t', ml) <- inferType ctx t
  insWeakTypeEnv x tl'
  -- Note that we cannot extend context with x. The type of e cannot be dependent on `x`.
  -- Otherwise the type of `mu x. e` might have `x` as free variable, which is unsound.
  (xtls', (e', tCod, mlPiCod)) <- inferBinder ctx xts e
  let (xts', mlPiArgs) = unzip xtls'
  mlPi <- newLevelOver m $ mlPiCod : mlPiArgs
  -- constrainList $ u : us
  let piType = (m, WeakTermPi xts' tCod)
  insConstraintEnv piType t'
  insConstraintEnv (asUniv ml) (asUniv mlPi)
  return ((m, WeakTermIter (mx, x, t') xts' e'), piType, mlPi)
  -- retWeakTerm piType m undefined $ WeakTermIter (mx, x, t') xts' e'
infer' ctx (m, WeakTermZeta x) = do
  (app, higherApp, ml) <- newHoleInCtx ctx m
  zenv <- gets zetaEnv
  case Map.lookup x zenv of
    Just (app', higherApp', ml') -> do
      insConstraintEnv app app'
      insConstraintEnv higherApp higherApp'
      insConstraintEnv (asUniv ml) (asUniv ml')
      return (app, higherApp, ml)
    Nothing -> do
      modify (\env -> env {zetaEnv = Map.insert x (app, higherApp, ml) zenv})
      return (app, higherApp, ml)
infer' _ (m, WeakTermConst x)
  -- enum.n8, enum.n64, etc.
  | Just i <- asEnumNatConstant x = do
    t <- toIsEnumType i m
    ml <- newLevelOver m []
    return ((m, WeakTermConst x), t, ml)
    -- retWeakTerm t m l $ WeakTermConst x
  -- i64, f16, u8, etc.
  | Just _ <- asLowTypeMaybe x
    -- u <- newUnivAt m
    -- l <- newUnivLevel
   = do
    ml0 <- newLevelOver m []
    ml1 <- newLevelOver m [ml0]
    -- fixme: parametrize constants over universes
    return ((m, WeakTermConst x), (asUniv ml0), ml1)
    -- retWeakTerm u m l $ WeakTermConst x
  | otherwise = do
    (t, UnivLevelPlus (_, l)) <- lookupWeakTypeEnv x
    return ((m, WeakTermConst x), t, UnivLevelPlus (m, l))
    -- retWeakTerm t m l $ WeakTermConst x
infer' ctx (m, WeakTermConstDecl (mx, x, t) e) = do
  tl'@(t', _) <- inferType ctx t
  insWeakTypeEnv x tl'
  -- the type of `e` doesn't depend on `x`
  (e', t'', ml) <- infer' ctx e
  return ((m, WeakTermConstDecl (mx, x, t') e'), t'', ml)
  -- retWeakTerm t'' m l $ WeakTermConstDecl (mx, x, t') e'
infer' _ (m, WeakTermInt t i) = do
  (t', UnivLevelPlus (_, l)) <- inferType [] t -- ctx == [] since t' should be i64, i8, etc. (i.e. t must be closed)
  return ((m, WeakTermInt t' i), t', UnivLevelPlus (m, l))
  -- retWeakTerm t' m l $ WeakTermInt t' i
infer' _ (m, WeakTermFloat16 f)
  -- let t = (m, WeakTermConst "f16")
 = do
  ml <- newLevelOver m []
  return ((m, WeakTermFloat16 f), (m, WeakTermConst "f16"), ml)
  -- l <- newUnivLevel
  -- retWeakTerm t m l $ WeakTermFloat16 f
infer' _ (m, WeakTermFloat32 f) = do
  ml <- newLevelOver m []
  return ((m, WeakTermFloat32 f), (m, WeakTermConst "f32"), ml)
  -- let t = (m, WeakTermConst "f32")
  -- l <- newUnivLevel
  -- retWeakTerm t m l $ WeakTermFloat32 f
infer' _ (m, WeakTermFloat64 f) = do
  ml <- newLevelOver m []
  return ((m, WeakTermFloat64 f), (m, WeakTermConst "f64"), ml)
  -- let t = (m, WeakTermConst "f64")
  -- l <- newUnivLevel
  -- retWeakTerm t m l $ WeakTermFloat64 f
infer' _ (m, WeakTermFloat t f) = do
  (t', UnivLevelPlus (_, l)) <- inferType [] t -- t must be closed
  -- (t', UnivLevelPlus _ l) <- inferType [] t -- ctx == [] since t' should be i64, i8, etc. (i.e. t must be closed)
  return ((m, WeakTermFloat t' f), t', UnivLevelPlus (m, l))
  -- retWeakTerm t' m l $ WeakTermFloat t' f
infer' _ (m, WeakTermEnum name)
  -- u <- newUnivAt m
  -- l <- newUnivLevel
 = do
  ml0 <- newLevelOver m []
  ml1 <- newLevelOver m [ml0]
  return ((m, WeakTermEnum name), asUniv ml0, ml1)
  -- retWeakTerm u m l $ WeakTermEnum name
infer' _ (m, WeakTermEnumIntro v) = do
  ml <- newLevelOver m []
  case v of
    EnumValueIntS size _ -> do
      let t = (m, WeakTermEnum (EnumTypeIntS size))
      return ((m, WeakTermEnumIntro v), t, ml)
      -- l <- newUnivLevel
      -- retWeakTerm t m l $ WeakTermEnumIntro v
    EnumValueIntU size _ -> do
      let t = (m, WeakTermEnum (EnumTypeIntU size))
      return ((m, WeakTermEnumIntro v), t, ml)
      -- let t = (m, WeakTermEnum (EnumTypeIntU size))
      -- l <- newUnivLevel
      -- retWeakTerm t m l $ WeakTermEnumIntro v
    EnumValueNat i _ -> do
      let t = (m, WeakTermEnum $ EnumTypeNat i)
      -- l <- newUnivLevel
      return ((m, WeakTermEnumIntro v), t, ml)
      -- retWeakTerm t m l $ WeakTermEnumIntro v
    EnumValueLabel l -> do
      k <- lookupKind l
      let t = (m, WeakTermEnum $ EnumTypeLabel k)
      return ((m, WeakTermEnumIntro v), t, ml)
      -- lu <- newUnivLevel
      -- retWeakTerm t m lu $ WeakTermEnumIntro v
infer' ctx (m, WeakTermEnumElim (e, t) les) = do
  (t'', ml'') <- inferType ctx t
  (e', t', ml') <- infer' ctx e
  insConstraintEnv t' t''
  insConstraintEnv (asUniv ml'') (asUniv ml')
  if null les
    then do
      (h, ml) <- newTypeHoleInCtx ctx m
      -- (h, UnivLevelPlus _ l) <- newTypeHoleInCtx ctx m
      return ((m, WeakTermEnumElim (e', t') []), h, ml) -- ex falso quodlibet
    else do
      let (ls, es) = unzip les
      -- tls <- catMaybes <$> mapM (inferWeakCase ctx) ls
      (ls', tls) <- unzip <$> mapM (inferWeakCase ctx) ls
      -- forM_ (zip (repeat t') tls) $ uncurry insConstraintEnv
      forM_ (zip (repeat t') tls) $ uncurry insConstraintEnv
      (es', ts, mls) <- unzip3 <$> mapM (infer' ctx) es
      constrainList $ ts
      constrainList $ map asUniv mls
      return ((m, WeakTermEnumElim (e', t') $ zip ls' es'), head ts, head mls)
      -- retWeakTerm (head ts) m undefined $
      --   WeakTermEnumElim (e', t') $ zip ls' es'
infer' ctx (m, WeakTermArray dom k) = do
  (dom', mlDom) <- inferType ctx dom
  ml0 <- newLevelOver m [mlDom]
  ml1 <- newLevelOver m [ml0]
  -- let univ = (m, WeakTermTau l)
  -- lu <- newUnivLevel
  -- let ml1 = UnivLevelPlus m lu
  -- modify (\env -> env {levelEnv = (ml, ml1) : levelEnv env})
  return ((m, WeakTermArray dom' k), asUniv ml0, ml1)
  -- retWeakTerm univ m lu $ WeakTermArray dom' k
infer' ctx (m, WeakTermArrayIntro k es) = do
  let tCod = inferKind k
  (es', ts, mls) <- unzip3 <$> mapM (infer' ctx) es
  forM_ (zip ts (repeat tCod)) $ uncurry insConstraintEnv
  constrainList $ map asUniv mls
  let len = toInteger $ length es
  let dom = (emptyMeta, WeakTermEnum (EnumTypeNat len))
  -- たぶんこのarrayの型が「左」にきて、んでarrayについての分解からこのdomのemptyMetaが左にきて、んで
  -- 位置情報が不明になる、って仕組みだと思う。はい。
  -- WeakTermArray dom1 k1 = WeakTermArray dom2 k2みたいな状況ね。
  let t = (m, WeakTermArray dom k)
  ml <- newLevelOver m mls
  return ((m, WeakTermArrayIntro k es'), t, ml)
  -- retWeakTerm t m undefined $ WeakTermArrayIntro k es'
infer' ctx (m, WeakTermArrayElim k xts e1 e2) = do
  (e1', t1, mlArr) <- infer' ctx e1
  (xtls', (e2', t2, ml2)) <- inferBinder ctx xts e2
  let (xts', mls) = unzip xtls'
  forM_ mls $ \mlArrArg -> insLevelLT mlArrArg mlArr
  -- このdomも位置がわからない。わからないというか、定義されない。
  let dom = (emptyMeta, WeakTermEnum (EnumTypeNat (toInteger $ length xts)))
  insConstraintEnv t1 (fst e1', WeakTermArray dom k)
  let ts = map (\(_, _, t) -> t) xts'
  forM_ (zip ts (repeat (inferKind k))) $ uncurry insConstraintEnv
  -- constrainList $ inferKind k : map snd xts'
  return ((m, WeakTermArrayElim k xts' e1' e2'), t2, ml2)
  -- retWeakTerm t2 m ml2 $ WeakTermArrayElim k xts' e1' e2'
infer' _ (m, WeakTermStruct ts) = do
  ml0 <- newLevelOver m []
  ml1 <- newLevelOver m [ml0]
  -- u <- newUnivAt m
  return ((m, WeakTermStruct ts), asUniv ml0, ml1)
  -- retWeakTerm u m undefined $ WeakTermStruct ts
infer' ctx (m, WeakTermStructIntro eks) = do
  let (es, ks) = unzip eks
  let ts = map inferKind ks
  let structType = (m, WeakTermStruct ks)
  (es', ts', mls) <- unzip3 <$> mapM (infer' ctx) es
  forM_ (zip ts' ts) $ uncurry insConstraintEnv
  ml <- newLevelOver m mls
  return ((m, WeakTermStructIntro $ zip es' ks), structType, ml)
  -- retWeakTerm structType m undefined $ WeakTermStructIntro $ zip es' ks
infer' ctx (m, WeakTermStructElim xks e1 e2) = do
  (e1', t1, mlStruct) <- infer' ctx e1
  let (ms, xs, ks) = unzip3 xks
  let ts = map inferKind ks
  -- fixme: add level constraint
  ls <- mapM (const newUnivLevel) ts
  let mls = map UnivLevelPlus $ zip (repeat m) ls
  forM_ mls $ \mlStructArg -> insLevelLT mlStructArg mlStruct
  let structType = (fst e1', WeakTermStruct ks)
  insConstraintEnv t1 structType
  let xts = zip3 ms xs ts
  -- forM_ (zip xs ts) $ uncurry insWeakTypeEnv
  forM_ (zip xs (zip ts mls)) $ uncurry insWeakTypeEnv
  (e2', t2, ml2) <- infer' (ctx ++ zip xts mls) e2
  -- (e2', t2) <- infer' (ctx ++ xts) e2
  return ((m, WeakTermStructElim xks e1' e2'), t2, ml2)
  -- retWeakTerm t2 m l2 $ WeakTermStructElim xks e1' e2'

-- {} inferType {}
inferType :: Context -> WeakTermPlus -> WithEnv (WeakTermPlus, UnivLevelPlus)
inferType ctx t = do
  (t', u, l) <- infer' ctx t
  ml <- newLevelOver (fst t') []
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
  (cod', lCod) <- inferType ctx cod
  return ([], (cod', lCod))
inferPi ctx ((mx, x, t):xts) cod = do
  tl'@(t', l) <- inferType ctx t
  insWeakTypeEnv x tl'
  (xtls', tlCod) <- inferPi (ctx ++ [((mx, x, t'), l)]) xts cod
  return (((mx, x, t'), l) : xtls', tlCod)

inferSigma ::
     Context -> [IdentifierPlus] -> WithEnv [(IdentifierPlus, UnivLevelPlus)]
inferSigma _ [] = return []
inferSigma ctx ((mx, x, t):xts) = do
  tl'@(t', l) <- inferType ctx t
  insWeakTypeEnv x tl'
  xts' <- inferSigma (ctx ++ [((mx, x, t'), l)]) xts
  return $ ((mx, x, t'), l) : xts'

-- {} inferBinder {}
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
  tl'@(t', l) <- inferType ctx t
  insWeakTypeEnv x tl'
  (xtls', etl') <- inferBinder (ctx ++ [((mx, x, t'), l)]) xts e
  return (((mx, x, t'), l) : xtls', etl')

-- {} inferPiElim {}
inferPiElim ::
     Context
  -> Meta
  -> (WeakTermPlus, WeakTermPlus, UnivLevelPlus)
  -> [(WeakTermPlus, WeakTermPlus, UnivLevelPlus)]
  -> WithEnv (WeakTermPlus, WeakTermPlus, UnivLevelPlus)
inferPiElim ctx m (e, t, mlPi) etls = do
  let (es, ts, mlPiDomList) = unzip3 etls
  -- case t of
  --   (_, WeakTermPi xts cod) -- performance optimization (not necessary for correctness)
  --     | length xts == length etls -> do
  --       let xs = map (\(_, x, _) -> x) xts
  --       let ts'' = map (\(_, _, tx) -> substWeakTermPlus (zip xs es) tx) xts
  --       forM_ (zip ts'' ts) $ uncurry insConstraintEnv
  --       -- forM_ (zip ts ts'') $ uncurry insConstraintEnv
  --       let cod' = substWeakTermPlus (zip xs es) cod
  --       return ((m, WeakTermPiElim e es), cod', undefined)
  --       -- retWeakTerm cod' m undefined $ WeakTermPiElim e es
  --   _ -> do
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
  forM_ (zip ts ts'') $ uncurry insConstraintEnv
  let us1 = map asUniv mlPiDomList
  let us2 = map asUniv mls'
  forM_ (zip us1 us2) $ uncurry insConstraintEnv
  (cod, mlPiCod) <- newTypeHoleInCtx (ctx ++ ytls) m
  -- mlPiCod < mlが成立するべき
  forM_ mlPiDomList $ \mlPiDom -> insLevelLT mlPiDom mlPi
  insLevelLT mlPiCod mlPi
  insConstraintEnv t (fst e, WeakTermPi yts cod)
  let cod' = substWeakTermPlus (zip ys es) cod
  return ((m, WeakTermPiElim e es), cod', mlPiCod)
  -- retWeakTerm cod' m undefined $ WeakTermPiElim e es

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
  tl@(t, l) <- newTypeHoleInCtx ctx m
  insWeakTypeEnv x tl
  ts <- newTypeHoleListInCtx (ctx ++ [((m, x, t), l)]) rest
  return $ ((m, x, t), l) : ts

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
  (t', _) <- inferType ctx t
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

-- retWeakTerm ::
--      WeakTermPlus
--   -> Meta
--   -> UnivLevel
--   -> WeakTerm
--   -> WithEnv (WeakTermPlus, WeakTermPlus, UnivLevelPlus)
-- retWeakTerm t m l e = return ((m, e), t, UnivLevelPlus m l)
-- is-enum n{i}
toIsEnumType :: Integer -> Meta -> WithEnv WeakTermPlus
toIsEnumType i m = do
  return
    ( m
    , WeakTermPiElim
        (emptyMeta, WeakTermConst "is-enum")
        [(emptyMeta, WeakTermEnum $ EnumTypeNat i)])

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

-- newUnivAt :: Meta -> WithEnv WeakTermPlus
-- newUnivAt m = do
--   l <- newUnivLevel
--   return (m, WeakTermTau l)
-- newLevelOver :: UnivLevelPlus -> WithEnv UnivLevel
-- newLevelOver ml0@(UnivLevelPlus m _) = do
--   l1 <- newUnivLevel
--   let ml1 = UnivLevelPlus m l1
--   modify (\env -> env {levelEnv = (ml0, ml1) : levelEnv env})
--   return l1
newLevelOver :: Meta -> [UnivLevelPlus] -> WithEnv UnivLevelPlus
newLevelOver m mls = do
  lu <- newUnivLevel
  let mlu = UnivLevelPlus (m, lu)
  forM_ mls $ \ml' -> insLevelLT ml' mlu
  return mlu

asUniv :: UnivLevelPlus -> WeakTermPlus
asUniv (UnivLevelPlus (m, l)) = (m, WeakTermTau l)

insLevelLT :: UnivLevelPlus -> UnivLevelPlus -> WithEnv ()
insLevelLT ml1 ml2 = modify (\env -> env {levelEnv = (ml1, ml2) : levelEnv env})
