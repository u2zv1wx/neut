module Elaborate.Infer
  ( infer
  , typeOf
  , univ
  , metaTerminal
  , insWeakTypeEnv
  ) where

import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes)

import Data.Basic
import Data.Env
import Data.QuasiTerm
import Data.WeakTerm

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
-- {termはrename済みでclosed} infer {termはrename済みでclosedで、かつすべてのsubtermが型でannotateされている}
-- type-annotationを与えるのがメインの挙動だけど、それ自体は型情報に記録されている。
infer :: Context -> QuasiTermPlus -> WithEnv WeakTermPlus
infer _ (m, QuasiTermTau) = return (PreMetaTerminal m, WeakTermTau)
infer _ (m, QuasiTermUpsilon x) = do
  t <- lookupWeakTypeEnv x
  retWeakTerm t m $ WeakTermUpsilon x
infer ctx (m, QuasiTermPi xts t) = do
  (xts', t') <- inferPi ctx xts t
  retWeakTerm univ m $ WeakTermPi xts' t'
infer ctx (m, QuasiTermPiIntro xts e) = do
  (xts', e') <- inferPiIntro ctx xts e
  let piType = (metaTerminal, WeakTermPi xts' (typeOf e'))
  retWeakTerm piType m $ WeakTermPiIntro xts' e'
infer ctx (m, QuasiTermPiElim e@(_, QuasiTermPiIntro xts _) es)
  | length xts == length es
    -- Consider the following code:
    --   (definition itself ((S tau)) S)
    --   (definition id ((A tau) (x A)) x)
    --   (ascription id
    --     (pi
    --       ((A tau)
    --        (x A))
    --       (itself A)))
    -- In the example code above, the type of `id` is inferred to be
    --   Pi (A : Tau, x : A). A,
    -- whereas the type ascription provided by the last term is
    --   Pi (A : Tau, x : A). itself @ (A).
    -- Without the information provided by `defList`, one of the resulting constraint
    -- `A == itself @ (A)` cannot be resolved since we don't know how to unfold the
    -- definition of `itself`. This case-split of PiElim is exactly for this purpose.
   = do
    es' <- mapM (infer ctx) es
    e' <- infer ctx e
    senv <- gets substEnv
    let hss = map holeWeakTermPlus es'
    let defList = zip (map fst xts) (zip hss es')
    modify (\env -> env {substEnv = defList ++ senv})
    inferPiElim ctx m e' es'
infer ctx (m, QuasiTermPiElim e es) = do
  es' <- mapM (infer ctx) es
  -- `es` must be inferred first since inference on `e` might extend the context,
  -- leading (for example) the type of a constant set to be something like ?M @ (ctx, x).
  -- This might cause a problem since if we have the same constant in `es`, the type of
  -- the constant is inferred to be ?M @ (ctx, x), despite the fact that the `x` is not in
  -- the context of the constant.
  e' <- infer ctx e
  inferPiElim ctx m e' es'
infer ctx (m, QuasiTermMu (x, t) e) = do
  t' <- inferType ctx t
  insWeakTypeEnv x t'
  -- Note that we cannot extend context with x. The type of e cannot be dependent on `x`.
  -- Otherwise the type of `mu x. e` might have `x` as free variable, which is unsound.
  e' <- infer ctx e
  insConstraintEnv t' (typeOf e')
  retWeakTerm t' m $ WeakTermMu (x, t') e'
infer ctx (m, QuasiTermZeta _) = do
  h <- newHoleInCtx ctx m
  return h
infer _ (m, QuasiTermConst x)
  -- enum.n8, enum.n64, etc.
  | Just i <- asEnumNatNumConstant x = do
    t' <- toIsEnumType i
    retWeakTerm t' m $ WeakTermConst x
  -- i64, f16, u8, etc.
  | Just _ <- asLowTypeMaybe x = retWeakTerm univ m $ WeakTermConst x
  | otherwise = do
    t <- lookupWeakTypeEnv x
    retWeakTerm t m $ WeakTermConst x
infer ctx (m, QuasiTermConstDecl (x, t) e) = do
  t' <- inferType ctx t
  insWeakTypeEnv x t'
  -- the type of `e` doesn't depend on `x`
  e' <- infer ctx e
  retWeakTerm (typeOf e') m $ WeakTermConstDecl (x, t') e'
infer _ (m, QuasiTermIntS size i) = do
  let t = (metaTerminal, WeakTermConst $ "i" ++ show size)
  retWeakTerm t m $ WeakTermIntS size i
infer _ (m, QuasiTermIntU size i) = do
  let t = (metaTerminal, WeakTermConst $ "u" ++ show size)
  retWeakTerm t m $ WeakTermIntU size i
infer ctx (m, QuasiTermInt i) = do
  h <- newTypeHoleInCtx ctx
  retWeakTerm h m $ WeakTermInt i
infer _ (m, QuasiTermFloat16 f) = do
  let t = (metaTerminal, WeakTermConst "f16")
  retWeakTerm t m $ WeakTermFloat16 f
infer _ (m, QuasiTermFloat32 f) = do
  let t = (metaTerminal, WeakTermConst "f32")
  retWeakTerm t m $ WeakTermFloat32 f
infer _ (m, QuasiTermFloat64 f) = do
  let t = (metaTerminal, WeakTermConst "f64")
  retWeakTerm t m $ WeakTermFloat64 f
infer ctx (m, QuasiTermFloat f) = do
  h <- newTypeHoleInCtx ctx
  retWeakTerm h m $ WeakTermFloat f
infer _ (m, QuasiTermEnum name) = retWeakTerm univ m $ WeakTermEnum name
infer _ (m, QuasiTermEnumIntro labelOrNum) = do
  case labelOrNum of
    EnumValueLabel l -> do
      k <- lookupKind l
      let t = (metaTerminal, WeakTermEnum $ EnumTypeLabel k)
      retWeakTerm t m $ WeakTermEnumIntro labelOrNum
    EnumValueNatNum i _ -> do
      let t = (metaTerminal, WeakTermEnum $ EnumTypeNatNum i)
      retWeakTerm t m $ WeakTermEnumIntro labelOrNum
infer ctx (m, QuasiTermEnumElim e les) = do
  e' <- infer ctx e
  if null les
    then do
      h <- newTypeHoleInCtx ctx
      retWeakTerm h m $ WeakTermEnumElim e' [] -- ex falso quodlibet
    else do
      let (ls, es) = unzip les
      tls <- mapM inferCase ls
      constrainList $ (typeOf e') : catMaybes tls
      es' <- mapM (infer ctx) es
      constrainList $ map typeOf es'
      retWeakTerm (typeOf $ head es') m $ WeakTermEnumElim e' $ zip ls es'
infer ctx (m, QuasiTermArray k indexType) = do
  indexType' <- inferType ctx indexType
  retWeakTerm univ m $ WeakTermArray k indexType'
infer ctx (m, QuasiTermArrayIntro k les) = do
  let (ls, es) = unzip les
  tls <- catMaybes <$> mapM (inferCase . CaseValue) ls
  constrainList tls
  let tCod = inferKind k
  es' <- mapM (infer ctx) es
  constrainList $ tCod : map typeOf es'
  let indexType = determineDomType tls
  let t = (metaTerminal, WeakTermArray k indexType)
  retWeakTerm t m $ WeakTermArrayIntro k $ zip ls es'
infer ctx (m, QuasiTermArrayElim k e1 e2) = do
  let tCod = inferKind k
  e1' <- infer ctx e1
  e2' <- infer ctx e2
  insConstraintEnv (typeOf e1') (metaTerminal, WeakTermArray k (typeOf e2'))
  retWeakTerm tCod m $ WeakTermArrayElim k e1' e2'

inferType :: Context -> QuasiTermPlus -> WithEnv WeakTermPlus
inferType ctx t = do
  t' <- infer ctx t
  insConstraintEnv (typeOf t') univ
  return t'

inferKind :: ArrayKind -> WeakTermPlus
inferKind (ArrayKindIntS i) = (metaTerminal, WeakTermConst $ "i" ++ show i)
inferKind (ArrayKindIntU i) = (metaTerminal, WeakTermConst $ "u" ++ show i)
inferKind (ArrayKindFloat size) =
  (metaTerminal, WeakTermConst $ "f" ++ show (sizeAsInt size))

inferPi ::
     Context
  -> [(Identifier, QuasiTermPlus)]
  -> QuasiTermPlus
  -> WithEnv ([(Identifier, WeakTermPlus)], WeakTermPlus)
inferPi ctx [] cod = do
  cod' <- inferType ctx cod
  return ([], cod')
inferPi ctx ((x, t):xts) cod = do
  t' <- inferType ctx t
  insWeakTypeEnv x t'
  (xts', cod') <- inferPi (ctx ++ [(x, t')]) xts cod
  return ((x, t') : xts', cod')

inferPiIntro ::
     Context
  -> [(Identifier, QuasiTermPlus)]
  -> QuasiTermPlus
  -> WithEnv ([(Identifier, WeakTermPlus)], WeakTermPlus)
inferPiIntro ctx [] e = do
  e' <- infer ctx e
  return ([], e')
inferPiIntro ctx ((x, t):xts) e = do
  t' <- inferType ctx t
  insWeakTypeEnv x t'
  (xts', e') <- inferPiIntro (ctx ++ [(x, t')]) xts e
  return ((x, t') : xts', e')

inferPiElim ::
     Context -> Meta -> WeakTermPlus -> [WeakTermPlus] -> WithEnv WeakTermPlus
inferPiElim ctx m e es = do
  ys <- mapM (const $ newNameWith "arg") es
  -- yts = [y1 : ?M1 @ (ctx[0], ..., ctx[n]),
  --        y2 : ?M2 @ (ctx[0], ..., ctx[n], y1),
  --        ...,
  --        ym : ?Mm @ (ctx[0], ..., ctx[n], y1, ..., y{m-1})]
  yts <- newTypeHoleListInCtx ctx ys
  let ts = map typeOf es
  -- ts' = [?M1 @ (ctx[0], ..., ctx[n]),
  --        ?M2 @ (ctx[0], ..., ctx[n], e1),
  --        ...,
  --        ?Mm @ (ctx[0], ..., ctx[n], e1, ..., e{m-1})]
  let ts' = map (substWeakTermPlus (zip ys es) . snd) yts
  forM_ (zip ts ts') $ uncurry insConstraintEnv
  cod <- newTypeHoleInCtx (ctx ++ yts)
  insConstraintEnv univ $ typeOf cod
  let tPi = (metaTerminal, WeakTermPi yts cod)
  insConstraintEnv tPi (typeOf e)
   -- cod' = ?M @ (ctx[0], ..., ctx[n], e1, ..., em)
  let cod' = substWeakTermPlus (zip ys es) cod
  retWeakTerm cod' m $ WeakTermPiElim e es

-- In a context (x1 : A1, ..., xn : An), this function creates metavariables
--   ?M  : Pi (x1 : A1, ..., xn : An). ?Mt @ (x1, ..., xn)
--   ?Mt : Pi (x1 : A1, ..., xn : An). Univ
-- and return ?M @ (x1, ..., xn) : ?Mt @ (x1, ..., xn).
-- Note that we can't just set `?M : Pi (x1 : A1, ..., xn : An). Univ` since
-- QuasiTermZeta might be used as an ordinary term, that is, a term which is not a type.
newHoleInCtx :: Context -> Meta -> WithEnv WeakTermPlus
newHoleInCtx ctx m = do
  higherHole <- newHoleOfType (metaTermWith m, WeakTermPi ctx univ)
  varSeq <- mapM (uncurry toVar) ctx
  let app = (metaTermWith m, WeakTermPiElim higherHole varSeq)
  hole <- newHoleOfType (metaTermWith m, WeakTermPi ctx app)
  return (PreMetaNonTerminal app m, WeakTermPiElim hole varSeq)

-- In a context (x1 : A1, ..., xn : An), this function creates a metavariable
--   ?M  : Pi (x1 : A1, ..., xn : An). Univ
-- and return ?M @ (x1, ..., xn) : Univ.
newTypeHoleInCtx :: Context -> WithEnv WeakTermPlus
newTypeHoleInCtx ctx = do
  varSeq <- mapM (uncurry toVar) ctx
  hole <- newHoleOfType (metaTerminal, WeakTermPi ctx univ)
  return (PreMetaNonTerminal univ emptyMeta, WeakTermPiElim hole varSeq)

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
     Context -> [Identifier] -> WithEnv [(Identifier, WeakTermPlus)]
newTypeHoleListInCtx _ [] = return []
newTypeHoleListInCtx ctx (x:rest) = do
  t <- newTypeHoleInCtx ctx
  insWeakTypeEnv x t
  ts <- newTypeHoleListInCtx (ctx ++ [(x, t)]) rest
  return $ (x, t) : ts

inferCase :: Case -> WithEnv (Maybe WeakTermPlus)
inferCase (CaseValue (EnumValueLabel name)) = do
  ienv <- gets enumEnv
  k <- lookupKind' name ienv
  return $ Just (metaTerminal, WeakTermEnum $ EnumTypeLabel k)
inferCase (CaseValue (EnumValueNatNum i _)) =
  return $ Just (metaTerminal, WeakTermEnum $ EnumTypeNatNum i)
inferCase _ = return Nothing

constrainList :: [WeakTermPlus] -> WithEnv ()
constrainList [] = return ()
constrainList [_] = return ()
constrainList (t1:t2:ts) = do
  insConstraintEnv t1 t2
  constrainList $ t2 : ts

toVar :: Identifier -> WeakTermPlus -> WithEnv WeakTermPlus
toVar x t = do
  insWeakTypeEnv x t
  return (PreMetaNonTerminal t emptyMeta, WeakTermUpsilon x)

retWeakTerm :: WeakTermPlus -> Meta -> WeakTerm -> WithEnv WeakTermPlus
retWeakTerm t ml e = return (PreMetaNonTerminal t ml, e)

-- is-enum n{i}
toIsEnumType :: Integer -> WithEnv WeakTermPlus
toIsEnumType i = do
  piType <- univToUniv
  let piMeta = PreMetaNonTerminal piType emptyMeta
  return
    ( metaTerminal
    , WeakTermPiElim
        (piMeta, WeakTermConst "is-enum")
        [(metaTerminal, WeakTermEnum $ EnumTypeNatNum i)])

-- Univ -> Univ
univToUniv :: WithEnv WeakTermPlus
univToUniv = do
  h <- newNameWith "hole-univ-to-univ"
  return (metaTerminal, WeakTermPi [(h, univ)] univ)

metaTerminal :: PreMeta
metaTerminal = PreMetaTerminal emptyMeta

metaTermWith :: Meta -> PreMeta
metaTermWith m = PreMetaTerminal m

newHoleOfType :: WeakTermPlus -> WithEnv WeakTermPlus
newHoleOfType t = do
  h <- newNameWith "hole-with-type"
  return (PreMetaNonTerminal t emptyMeta, WeakTermZeta h)

determineDomType :: [WeakTermPlus] -> WeakTermPlus
determineDomType ts =
  if not (null ts)
    then head ts
    else (metaTerminal, WeakTermConst "bottom")

insConstraintEnv :: WeakTermPlus -> WeakTermPlus -> WithEnv ()
insConstraintEnv t1 t2 =
  modify (\e -> e {constraintEnv = (t1, t2) : constraintEnv e})

insWeakTypeEnv :: Identifier -> WeakTermPlus -> WithEnv ()
insWeakTypeEnv i t =
  modify (\e -> e {weakTypeEnv = Map.insert i t (weakTypeEnv e)})

lookupWeakTypeEnv :: String -> WithEnv WeakTermPlus
lookupWeakTypeEnv s = do
  mt <- lookupWeakTypeEnvMaybe s
  case mt of
    Just t -> return t
    Nothing -> throwError $ s ++ " is not found in the type environment."

lookupWeakTypeEnvMaybe :: String -> WithEnv (Maybe WeakTermPlus)
lookupWeakTypeEnvMaybe s = do
  mt <- gets (Map.lookup s . weakTypeEnv)
  case mt of
    Nothing -> return Nothing
    Just t -> return $ Just t

lookupKind :: Identifier -> WithEnv Identifier
lookupKind name = do
  env <- get
  lookupKind' name $ enumEnv env

lookupKind' :: Identifier -> [(Identifier, [Identifier])] -> WithEnv Identifier
lookupKind' i [] = throwError $ "no such enum-intro is defined: " ++ i
lookupKind' i ((j, ls):xs) =
  if i `elem` ls
    then return j
    else lookupKind' i xs
