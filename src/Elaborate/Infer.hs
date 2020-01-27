{-# LANGUAGE OverloadedStrings #-}

module Elaborate.Infer
  ( infer
  , univ
  , insWeakTypeEnv
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.Basic
import Data.Env
import Data.Maybe (catMaybes)
import Data.WeakTerm

import qualified Data.HashMap.Strict as Map
import qualified Data.Text as T

type Context = [(Identifier, WeakTermPlus)]

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
  (e', _) <- infer' [] e
  let vs = varWeakTermPlus e'
  let info = toInfo "inferred term is not closed. freevars:" vs
  -- senv <- gets substEnv
  -- p' senv
  return $ assertP info e' $ null vs

infer' :: Context -> WeakTermPlus -> WithEnv (WeakTermPlus, WeakTermPlus)
infer' _ tau@(_, WeakTermTau) = return (tau, tau)
infer' _ (m, WeakTermUpsilon x)
  -- (_, t) <- lookupWeakTypeEnv x
  -- retWeakTerm (m, t) m $ WeakTermUpsilon x
 = do
  t <- lookupWeakTypeEnv x
  retWeakTerm t m $ WeakTermUpsilon x
infer' ctx (m, WeakTermPi xts t) = do
  (xts', t') <- inferPi ctx xts t
  retWeakTerm (univAt m) m $ WeakTermPi xts' t'
infer' ctx (m, WeakTermPiIntro xts e) = do
  (xts', (e', tCod)) <- inferBinder ctx xts e
  let piType = (m, WeakTermPi xts' tCod)
  retWeakTerm piType m $ WeakTermPiIntro xts' e'
infer' ctx (m, WeakTermPiElim (mPi, WeakTermPiIntro xts e) es) -- "let"
  | length xts == length es = do
    ets <- mapM (infer' ctx) es
    let (xs, ts) = unzip xts
    -- don't extend context
    ts' <- mapM (inferType ctx) ts
    let xts' = zip xs ts'
    forM_ xts' $ uncurry insWeakTypeEnv
    -- ctxをextendしなくてもdefListにそれ相当の情報がある
    (e', tCod) <- infer' ctx e -- don't extend context
    let piType = (mPi, WeakTermPi xts' tCod)
    et <- retWeakTerm piType mPi $ WeakTermPiIntro xts' e'
    let es' = map fst ets
    let defList = Map.fromList $ zip xs es'
    modify (\env -> env {substEnv = defList `Map.union` substEnv env})
    inferPiElim ctx m et ets
infer' ctx (m, WeakTermPiElim e es) = do
  ets <- mapM (infer' ctx) es
  et <- infer' ctx e
  inferPiElim ctx m et ets
infer' ctx (m, WeakTermSigma xts) = do
  xts' <- inferSigma ctx xts
  retWeakTerm (univAt m) m $ WeakTermSigma xts'
infer' ctx (m, WeakTermSigmaIntro t es) = do
  t' <- inferType ctx t
  (es', ts) <- unzip <$> mapM (infer' ctx) es
  ys <- mapM (const $ newNameWith "arg") es'
  -- yts = [(y1, ?M1 @ (ctx[0], ..., ctx[n])),
  --        (y2, ?M2 @ (ctx[0], ..., ctx[n], y1)),
  --        ...,
  --        (ym, ?Mm @ (ctx[0], ..., ctx[n], y1, ..., y{m-1}))]
  yts <- newTypeHoleListInCtx ctx $ zip ys (map fst es')
  let sigmaType = (m, WeakTermSigma yts)
  -- ts' = [?M1 @ (ctx[0], ..., ctx[n]),
  --        ?M2 @ (ctx[0], ..., ctx[n], e1),
  --        ...,
  --        ?Mm @ (ctx[0], ..., ctx[n], e1, ..., e{m-1})]
  let ts' = map (substWeakTermPlus (zip ys es) . snd) yts
  forM_ ((sigmaType, t') : zip ts ts') $ uncurry insConstraintEnv
  retWeakTerm sigmaType m $ WeakTermSigmaIntro t' es'
infer' ctx (m, WeakTermSigmaElim t xts e1 e2) = do
  t' <- inferType ctx t
  (e1', t1) <- infer' ctx e1
  xts' <- inferSigma ctx xts
  let sigmaType = (fst e1', WeakTermSigma xts')
  insConstraintEnv t1 sigmaType
  (e2', t2) <- infer' (ctx ++ xts') e2
  insConstraintEnv t2 t'
  retWeakTerm t2 m $ WeakTermSigmaElim t' xts' e1' e2'
infer' ctx (m, WeakTermIter (x, t) xts e) = do
  t' <- inferType ctx t
  insWeakTypeEnv x t'
  -- Note that we cannot extend context with x. The type of e cannot be dependent on `x`.
  -- Otherwise the type of `mu x. e` might have `x` as free variable, which is unsound.
  (xts', (e', tCod)) <- inferBinder ctx xts e
  let piType = (m, WeakTermPi xts' tCod)
  insConstraintEnv piType t'
  retWeakTerm piType m $ WeakTermIter (x, t') xts' e'
infer' ctx (m, WeakTermZeta x) = do
  (app, higherApp) <- newHoleInCtx ctx m
  zenv <- gets zetaEnv
  case Map.lookup x zenv of
    Just (app', higherApp') -> do
      insConstraintEnv app app'
      insConstraintEnv higherApp higherApp'
      return (app, higherApp)
    Nothing -> do
      modify (\env -> env {zetaEnv = Map.insert x (app, higherApp) zenv})
      return (app, higherApp)
infer' _ (m, WeakTermConst x)
  -- enum.n8, enum.n64, etc.
  | Just i <- asEnumNatConstant x = do
    t <- toIsEnumType i m
    retWeakTerm t m $ WeakTermConst x
  -- i64, f16, u8, etc.
  | Just _ <- asLowTypeMaybe x = retWeakTerm (univAt m) m $ WeakTermConst x
  | otherwise = do
    t <- lookupWeakTypeEnv x
    retWeakTerm t m $ WeakTermConst x
infer' ctx (m, WeakTermConstDecl (x, t) e) = do
  t' <- inferType ctx t
  insWeakTypeEnv x t'
  -- the type of `e` doesn't depend on `x`
  (e', t'') <- infer' ctx e
  retWeakTerm t'' m $ WeakTermConstDecl (x, t') e'
infer' _ (m, WeakTermInt t i) = do
  t' <- inferType [] t -- ctx == [] since t' should be i64, i8, etc. (i.e. t must be closed)
  retWeakTerm t' m $ WeakTermInt t' i
infer' _ (m, WeakTermFloat16 f) = do
  let t = (m, WeakTermConst "f16")
  retWeakTerm t m $ WeakTermFloat16 f
infer' _ (m, WeakTermFloat32 f) = do
  let t = (m, WeakTermConst "f32")
  retWeakTerm t m $ WeakTermFloat32 f
infer' _ (m, WeakTermFloat64 f) = do
  let t = (m, WeakTermConst "f64")
  retWeakTerm t m $ WeakTermFloat64 f
infer' _ (m, WeakTermFloat t f) = do
  t' <- inferType [] t -- t must be closed
  retWeakTerm t' m $ WeakTermFloat t' f
infer' _ (m, WeakTermEnum name) = retWeakTerm (univAt m) m $ WeakTermEnum name
infer' _ (m, WeakTermEnumIntro v) = do
  case v of
    EnumValueIntS size _ -> do
      let t = (m, WeakTermEnum (EnumTypeIntS size))
      retWeakTerm t m $ WeakTermEnumIntro v
    EnumValueIntU size _ -> do
      let t = (m, WeakTermEnum (EnumTypeIntU size))
      retWeakTerm t m $ WeakTermEnumIntro v
    EnumValueNat i _ -> do
      let t = (m, WeakTermEnum $ EnumTypeNat i)
      retWeakTerm t m $ WeakTermEnumIntro v
    EnumValueLabel l -> do
      k <- lookupKind l
      let t = (m, WeakTermEnum $ EnumTypeLabel k)
      retWeakTerm t m $ WeakTermEnumIntro v
infer' ctx (m, WeakTermEnumElim (e, t) les) = do
  t'' <- inferType ctx t
  (e', t') <- infer' ctx e
  insConstraintEnv t' t''
  if null les
    then do
      h <- newTypeHoleInCtx ctx m
      retWeakTerm h m $ WeakTermEnumElim (e', t') [] -- ex falso quodlibet
    else do
      let (ls, _) = unzip les
      tls <- catMaybes <$> mapM inferCase ls
      forM_ (zip (repeat t') tls) $ uncurry insConstraintEnv
      -- constrainList $ t' : catMaybes tls
      (es', ts) <- unzip <$> mapM (inferEnumElim ctx (e', t')) les
      constrainList $ ts
      retWeakTerm (head ts) m $ WeakTermEnumElim (e', t') $ zip ls es'
infer' ctx (m, WeakTermArray dom k) = do
  dom' <- inferType ctx dom
  retWeakTerm (univAt m) m $ WeakTermArray dom' k
infer' ctx (m, WeakTermArrayIntro k es) = do
  let tCod = inferKind k
  (es', ts) <- unzip <$> mapM (infer' ctx) es
  forM_ (zip ts (repeat tCod)) $ uncurry insConstraintEnv
  -- constrainList $ tCod : ts
  let len = toInteger $ length es
  -- このdomの場所って何、という話がある。mでいいのか？
  -- esの最初のやつとか？(array-intro u8 e1 e2 e3)とかだったら、e1の最初の位置。
  -- 微妙だな〜。それとも構文を(array-intro n3 u8 e1 e2 e3)とかにしたほうが素直なのか？
  -- こうしたらdomがわかりやすくなるが。
  -- 実際にtermを書くときには(array-intro _ u8 e1 e2 e3)とかって書けばよくて。
  -- まーでもそれをnotationで隠したりすると結局metaが意味不明に。
  let dom = (emptyMeta, WeakTermEnum (EnumTypeNat len))
  -- たぶんこのarrayの型が「左」にきて、んでarrayについての分解からこのdomのemptyMetaが左にきて、んで
  -- 位置情報が不明になる、って仕組みだと思う。はい。
  -- WeakTermArray dom1 k1 = WeakTermArray dom2 k2みたいな状況ね。
  let t = (m, WeakTermArray dom k)
  retWeakTerm t m $ WeakTermArrayIntro k es'
infer' ctx (m, WeakTermArrayElim k xts e1 e2) = do
  (e1', t1) <- infer' ctx e1
  (xts', (e2', t2)) <- inferBinder ctx xts e2
  let len = toInteger $ length xts
  -- このdomも位置がわからない。わからないというか、定義されない。
  let dom = (emptyMeta, WeakTermEnum (EnumTypeNat len))
  insConstraintEnv t1 (fst e1', WeakTermArray dom k)
  forM_ (zip (map snd xts') (repeat (inferKind k))) $ uncurry insConstraintEnv
  -- constrainList $ inferKind k : map snd xts'
  retWeakTerm t2 m $ WeakTermArrayElim k xts' e1' e2'
infer' _ (m, WeakTermStruct ts) = retWeakTerm (univAt m) m $ WeakTermStruct ts
infer' ctx (m, WeakTermStructIntro eks) = do
  let (es, ks) = unzip eks
  let ts = map inferKind ks
  let structType = (m, WeakTermStruct ks)
  (es', ts') <- unzip <$> mapM (infer' ctx) es
  forM_ (zip ts' ts) $ uncurry insConstraintEnv
  retWeakTerm structType m $ WeakTermStructIntro $ zip es' ks
infer' ctx (m, WeakTermStructElim xks e1 e2) = do
  (e1', t1) <- infer' ctx e1
  let (xs, ks) = unzip xks
  let ts = map inferKind ks
  let structType = (fst e1', WeakTermStruct ks)
  insConstraintEnv t1 structType
  let xts = zip xs ts
  forM_ xts $ uncurry insWeakTypeEnv
  (e2', t2) <- infer' (ctx ++ xts) e2
  retWeakTerm t2 m $ WeakTermStructElim xks e1' e2'

-- {} inferType {}
inferType :: Context -> WeakTermPlus -> WithEnv WeakTermPlus
inferType ctx t = do
  (t', u) <- infer' ctx t
  insConstraintEnv u univ
  return t'

-- {} inferKind {}
inferKind :: ArrayKind -> WeakTermPlus
inferKind (ArrayKindIntS i) = (emptyMeta, WeakTermEnum (EnumTypeIntS i))
inferKind (ArrayKindIntU i) = (emptyMeta, WeakTermEnum (EnumTypeIntU i))
inferKind (ArrayKindFloat size) =
  (emptyMeta, WeakTermConst $ "f" <> T.pack (show (sizeAsInt size)))
inferKind _ = error "inferKind for void-pointer"

-- {} inferPi {}
inferPi ::
     Context
  -> [(Identifier, WeakTermPlus)]
  -> WeakTermPlus
  -> WithEnv ([(Identifier, WeakTermPlus)], WeakTermPlus)
inferPi ctx [] cod = do
  cod' <- inferType ctx cod
  return ([], cod')
inferPi ctx ((x, t):xts) cod = do
  t' <- inferType ctx t
  insWeakTypeEnv x t'
  (xts', cod') <- inferPi (ctx ++ [(x, t')]) xts cod
  return ((x, t') : xts', cod')

inferSigma ::
     Context
  -> [(Identifier, WeakTermPlus)]
  -> WithEnv [(Identifier, WeakTermPlus)]
inferSigma _ [] = return []
inferSigma ctx ((x, t):xts) = do
  t' <- inferType ctx t
  insWeakTypeEnv x t'
  xts' <- inferSigma (ctx ++ [(x, t')]) xts
  return $ (x, t') : xts'

-- {} inferBinder {}
inferBinder ::
     Context
  -> [(Identifier, WeakTermPlus)]
  -> WeakTermPlus
  -> WithEnv ([(Identifier, WeakTermPlus)], (WeakTermPlus, WeakTermPlus))
inferBinder ctx [] e = do
  et' <- infer' ctx e
  return ([], et')
inferBinder ctx ((x, t):xts) e = do
  t' <- inferType ctx t
  insWeakTypeEnv x t'
  (xts', et') <- inferBinder (ctx ++ [(x, t')]) xts e
  return ((x, t') : xts', et')

-- {} inferPiElim {}
inferPiElim ::
     Context
  -> Meta
  -> (WeakTermPlus, WeakTermPlus)
  -> [(WeakTermPlus, WeakTermPlus)]
  -> WithEnv (WeakTermPlus, WeakTermPlus)
inferPiElim ctx m (e, t) ets = do
  let (es, ts) = unzip ets
  case t of
    (_, WeakTermPi xts cod) -- performance optimization (not necessary for correctness)
      | length xts == length ets -> do
        let xs = map fst xts
        let ts' = map (substWeakTermPlus (zip xs es) . snd) xts
        -- p "pi-elim-opt"
        -- p "constraints:"
        -- p' $ zip ts ts'
        -- let ms1 = map (showMeta . fst) ts
        -- let ms2 = map (showMeta . fst) ts'
        -- p "meta-info:"
        -- p' $ zip ms1 ms2
        forM_ (zip ts ts') $ uncurry insConstraintEnv
        -- p "done"
        let cod' = substWeakTermPlus (zip xs es) cod
        retWeakTerm cod' m $ WeakTermPiElim e es
    _ -> do
      ys <- mapM (const $ newNameWith "arg") es
      -- yts = [(y1, ?M1 @ (ctx[0], ..., ctx[n])),
      --        (y2, ?M2 @ (ctx[0], ..., ctx[n], y1)),
      --        ...,
      --        (ym, ?Mm @ (ctx[0], ..., ctx[n], y1, ..., y{m-1}))]
      yts <- newTypeHoleListInCtx ctx $ zip ys (map fst es)
      -- ts' = [?M1 @ (ctx[0], ..., ctx[n]),
      --        ?M2 @ (ctx[0], ..., ctx[n], e1),
      --        ...,
      --        ?Mm @ (ctx[0], ..., ctx[n], e1, ..., e{m-1})]
      let ts' = map (substWeakTermPlus (zip ys es) . snd) yts
      forM_ (zip ts ts') $ uncurry insConstraintEnv
      cod <- newTypeHoleInCtx (ctx ++ yts) m
      let tPi = (fst e, WeakTermPi yts cod)
      insConstraintEnv t tPi
      let cod' = substWeakTermPlus (zip ys es) cod
      retWeakTerm cod' m $ WeakTermPiElim e es

inferEnumElim ::
     Context
  -> (WeakTermPlus, WeakTermPlus)
  -> (Case, WeakTermPlus)
  -> WithEnv (WeakTermPlus, WeakTermPlus)
inferEnumElim ctx _ (CaseDefault, e) = infer' ctx e
inferEnumElim ctx ((m, WeakTermUpsilon x), enumType) (CaseValue v, e) = do
  x' <- newNameWith x
  -- infer `let xi := v in e{x := xi}`, with replacing all the occurrences of
  -- `x` in the type of `e{x := xi}` with `xi`.
  -- ctx must be extended since we're emulating the inference of `e{x := xi}` in `let xi := v in e{x := xi}`.
  let ctx' = ctx ++ [(x', enumType)]
  -- emulate the inference of the `let` part of `let xi := v in e{x := xi}`
  let val = (m, WeakTermEnumIntro v)
  modify (\env -> env {substEnv = Map.insert x' val (substEnv env)})
  -- the `e{x := xi}` part
  let var = (m, WeakTermUpsilon x')
  (e', t) <- infer' ctx' $ substWeakTermPlus [(x, var)] e
  let t' = substWeakTermPlus [(x, var)] t
  -- return `let xi := v in e{x := xi}`
  let e'' =
        ( emptyMeta
        , WeakTermPiElim
            (emptyMeta, WeakTermPiIntro [(x', enumType)] e')
            [(emptyMeta, WeakTermEnumIntro v)])
  return (e'', t')
inferEnumElim ctx _ (_, e) = infer' ctx e

-- In a context (x1 : A1, ..., xn : An), this function creates metavariables
--   ?M  : Pi (x1 : A1, ..., xn : An). ?Mt @ (x1, ..., xn)
--   ?Mt : Pi (x1 : A1, ..., xn : An). Univ
-- and return ?M @ (x1, ..., xn) : ?Mt @ (x1, ..., xn).
-- Note that we can't just set `?M : Pi (x1 : A1, ..., xn : An). Univ` since
-- WeakTermZeta might be used as an ordinary term, that is, a term which is not a type.
-- {} newHoleInCtx {}
newHoleInCtx :: Context -> Meta -> WithEnv (WeakTermPlus, WeakTermPlus)
newHoleInCtx ctx m = do
  higherHole <- newHole
  let varSeq = map (toVar . fst) ctx
  let higherApp = (m, WeakTermPiElim higherHole varSeq)
  hole <- newHole
  let app = (m, WeakTermPiElim hole varSeq)
  return (app, higherApp)

-- In a context (x1 : A1, ..., xn : An), this function creates a metavariable
--   ?M  : Pi (x1 : A1, ..., xn : An). Univ
-- and return ?M @ (x1, ..., xn) : Univ.
newTypeHoleInCtx :: Context -> Meta -> WithEnv WeakTermPlus
newTypeHoleInCtx ctx m = do
  let varSeq = map (toVar . fst) ctx
  hole <- newHole
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
     Context -> [(Identifier, Meta)] -> WithEnv [(Identifier, WeakTermPlus)]
newTypeHoleListInCtx _ [] = return []
newTypeHoleListInCtx ctx ((x, m):rest) = do
  t <- newTypeHoleInCtx ctx m
  insWeakTypeEnv x t
  ts <- newTypeHoleListInCtx (ctx ++ [(x, t)]) rest
  return $ (x, t) : ts

-- caseにもmetaの情報がほしいか。それはたしかに？
inferCase :: Case -> WithEnv (Maybe WeakTermPlus)
inferCase (CaseValue (EnumValueLabel name)) = do
  k <- lookupKind name
  return $ Just (emptyMeta, WeakTermEnum $ EnumTypeLabel k)
inferCase (CaseValue (EnumValueNat i _)) =
  return $ Just (emptyMeta, WeakTermEnum $ EnumTypeNat i)
inferCase (CaseValue (EnumValueIntS size _)) =
  return $ Just (emptyMeta, WeakTermEnum (EnumTypeIntS size))
inferCase (CaseValue (EnumValueIntU size _)) =
  return $ Just (emptyMeta, WeakTermEnum (EnumTypeIntU size))
inferCase CaseDefault = return Nothing

-- inferCase _ = return Nothing
constrainList :: [WeakTermPlus] -> WithEnv ()
constrainList [] = return ()
constrainList [_] = return ()
constrainList (t1:t2:ts) = do
  insConstraintEnv t1 t2
  constrainList $ t2 : ts

retWeakTerm ::
     WeakTermPlus -> Meta -> WeakTerm -> WithEnv (WeakTermPlus, WeakTermPlus)
retWeakTerm t m e = return ((m, e), t)

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

insWeakTypeEnv :: Identifier -> WeakTermPlus -> WithEnv ()
insWeakTypeEnv i t =
  modify (\e -> e {weakTypeEnv = Map.insert i t (weakTypeEnv e)})

lookupWeakTypeEnv :: Identifier -> WithEnv WeakTermPlus
lookupWeakTypeEnv s = do
  mt <- lookupWeakTypeEnvMaybe s
  case mt of
    Just t -> return t
    Nothing -> throwError' $ s <> " is not found in the weak type environment."

lookupWeakTypeEnvMaybe :: Identifier -> WithEnv (Maybe WeakTermPlus)
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
    Just j -> return j
