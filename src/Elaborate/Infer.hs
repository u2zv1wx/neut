module Elaborate.Infer
  ( infer
  , typeOf
  , univ
  , metaTerminal
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.Maybe (catMaybes)
import Prelude hiding (pi)

import Data.Basic
import Data.Env
import Data.PreTerm
import Data.WeakTerm

type Context = [(Identifier, PreTermPlus)]

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
-- infer e ~> {type-annotated e}
infer :: Context -> WeakTermPlus -> WithEnv PreTermPlus
infer _ (m, WeakTermTau) = return (PreMetaTerminal (toLoc m), PreTermTau)
infer ctx (m, WeakTermTheta x)
  | Just i <- asEnumNatNumConstant x = do
    t <- toIsEnumType i
    retPreTerm t (toLoc m) $ PreTermTheta x
  | otherwise = do
    mt <- lookupWeakTypeEnvMaybe x
    case mt of
      Just t -> retPreTerm t (toLoc m) $ PreTermTheta x
      Nothing -> do
        h <- newTypeHoleInCtx ctx
        insWeakTypeEnv x h
        retPreTerm h (toLoc m) $ PreTermTheta x
infer _ (m, WeakTermUpsilon x) = do
  t <- lookupWeakTypeEnv x
  retPreTerm t (toLoc m) $ PreTermUpsilon x
infer ctx (m, WeakTermPi xts t) = do
  (xts', t') <- inferPi ctx xts t
  retPreTerm univ (toLoc m) $ PreTermPi xts' t'
infer ctx (m, WeakTermPiIntro xts e) = do
  (xts', e') <- inferPiIntro ctx xts e
  let piType = (metaTerminal, PreTermPi xts' (typeOf e'))
  retPreTerm piType (toLoc m) $ PreTermPiIntro xts' e'
infer ctx (m, WeakTermPiElim e@(_, WeakTermPiIntro xts _) es)
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
    e' <- infer ctx e
    es' <- mapM (infer ctx) es
    senv <- gets substEnv
    let defList = zip (map fst xts) es'
    modify (\env -> env {substEnv = defList ++ senv})
    inferPiElim ctx m e' es'
infer ctx (m, WeakTermPiElim e es) = do
  e' <- infer ctx e
  es' <- mapM (infer ctx) es
  inferPiElim ctx m e' es'
infer ctx (m, WeakTermMu (x, t) e) = do
  t' <- inferType ctx t
  insWeakTypeEnv x t'
  e' <- infer (ctx ++ [(x, t')]) e
  insConstraintEnv t' (typeOf e')
  retPreTerm t' (toLoc m) $ PreTermMu (x, t') e'
infer ctx (_, WeakTermZeta _) = do
  h <- newHoleInCtx ctx
  return h
  -- insWeakTypeEnv x h
  -- retPreTerm (typeOf h) (toLoc m) (snd h)
  -- mt <- lookupWeakTypeEnvMaybe x
  -- case mt of
  --   Just t -> retPreTerm t (toLoc m) $ PreTermZeta x
  --   Nothing -> do
  --     h <- newTypeHoleInCtx ctx
  --     insWeakTypeEnv x h
  --     retPreTerm h (toLoc m) $ PreTermZeta x
infer _ (m, WeakTermIntS size i) = do
  let t = (metaTerminal, PreTermTheta $ "i" ++ show size)
  retPreTerm t (toLoc m) $ PreTermIntS size i
infer _ (m, WeakTermIntU size i) = do
  let t = (metaTerminal, PreTermTheta $ "u" ++ show size)
  retPreTerm t (toLoc m) $ PreTermIntU size i
infer ctx (m, WeakTermInt i) = do
  h <- newTypeHoleInCtx ctx
  retPreTerm h (toLoc m) $ PreTermInt i
infer _ (m, WeakTermFloat16 f) = do
  let t = (metaTerminal, PreTermTheta "f16")
  retPreTerm t (toLoc m) $ PreTermFloat16 f
infer _ (m, WeakTermFloat32 f) = do
  let t = (metaTerminal, PreTermTheta "f32")
  retPreTerm t (toLoc m) $ PreTermFloat32 f
infer _ (m, WeakTermFloat64 f) = do
  let t = (metaTerminal, PreTermTheta "f64")
  retPreTerm t (toLoc m) $ PreTermFloat64 f
infer ctx (m, WeakTermFloat f) = do
  h <- newTypeHoleInCtx ctx
  retPreTerm h (toLoc m) $ PreTermFloat f
infer _ (m, WeakTermEnum name) = retPreTerm univ (toLoc m) $ PreTermEnum name
infer _ (m, WeakTermEnumIntro labelOrNum) = do
  case labelOrNum of
    EnumValueLabel l -> do
      k <- lookupKind l
      let t = (metaTerminal, PreTermEnum $ EnumTypeLabel k)
      retPreTerm t (toLoc m) $ PreTermEnumIntro labelOrNum
    EnumValueNatNum i _ -> do
      let t = (metaTerminal, PreTermEnum $ EnumTypeNatNum i)
      retPreTerm t (toLoc m) $ PreTermEnumIntro labelOrNum
infer ctx (m, WeakTermEnumElim e les) = do
  e' <- infer ctx e
  if null les
    then do
      h <- newTypeHoleInCtx ctx
      retPreTerm h (toLoc m) $ PreTermEnumElim e' [] -- ex falso quodlibet
    else do
      let (ls, es) = unzip les
      tls <- mapM inferCase ls
      constrainList $ (typeOf e') : catMaybes tls
      es' <- mapM (infer ctx) es
      constrainList $ map typeOf es'
      retPreTerm (typeOf $ head es') (toLoc m) $ PreTermEnumElim e' $ zip ls es'
infer ctx (m, WeakTermArray k indexType) = do
  indexType' <- inferType ctx indexType
  retPreTerm univ (toLoc m) $ PreTermArray k indexType'
infer ctx (m, WeakTermArrayIntro k les) = do
  let (ls, es) = unzip les
  tls <- catMaybes <$> mapM (inferCase . CaseValue) ls
  constrainList tls
  let tCod = inferKind k
  es' <- mapM (infer ctx) es
  constrainList $ tCod : map typeOf es'
  let indexType = determineDomType tls
  let t = (metaTerminal, PreTermArray k indexType)
  retPreTerm t (toLoc m) $ PreTermArrayIntro k $ zip ls es'
infer ctx (m, WeakTermArrayElim k e1 e2) = do
  let tCod = inferKind k
  e1' <- infer ctx e1
  e2' <- infer ctx e2
  insConstraintEnv (typeOf e1') (metaTerminal, PreTermArray k (typeOf e2'))
  retPreTerm tCod (toLoc m) $ PreTermArrayElim k e1' e2'

inferType :: Context -> WeakTermPlus -> WithEnv PreTermPlus
inferType ctx t = do
  t' <- infer ctx t
  insConstraintEnv (typeOf t') univ
  return t'

inferKind :: ArrayKind -> PreTermPlus
inferKind (ArrayKindIntS i) = (metaTerminal, PreTermTheta $ "i" ++ show i)
inferKind (ArrayKindIntU i) = (metaTerminal, PreTermTheta $ "u" ++ show i)
inferKind (ArrayKindFloat size) =
  (metaTerminal, PreTermTheta $ "f" ++ show (sizeAsInt size))

inferPi ::
     Context
  -> [(Identifier, WeakTermPlus)]
  -> WeakTermPlus
  -> WithEnv ([(Identifier, PreTermPlus)], PreTermPlus)
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
  -> [(Identifier, WeakTermPlus)]
  -> WeakTermPlus
  -> WithEnv ([(Identifier, PreTermPlus)], PreTermPlus)
inferPiIntro ctx [] e = do
  e' <- infer ctx e
  return ([], e')
inferPiIntro ctx ((x, t):xts) e = do
  t' <- inferType ctx t
  insWeakTypeEnv x t'
  (xts', e') <- inferPiIntro (ctx ++ [(x, t')]) xts e
  return ((x, t') : xts', e')

inferPiElim ::
     Context -> WeakMeta -> PreTermPlus -> [PreTermPlus] -> WithEnv PreTermPlus
inferPiElim ctx m e es
  -- t' <- reducePreTermPlus $ typeOf e
  -- -- この場合分けをしても別に解けるものが増えるわけではないらしい
  -- case t' of
  --   (_, PreTermPi xts cod) -> do
  --     let (xs, ts) = unzip xts
  --     p "shortcut"
  --     let ts' = map (substPreTermPlus (zip xs es)) ts
  --     forM_ (zip ts' (map typeOf es)) $ uncurry insConstraintEnv
  --     let cod' = substPreTermPlus (zip xs es) cod
  --     retPreTerm cod' (toLoc m) $ PreTermPiElim e es
  --   _ -> do
 = do
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
  let ts' = map (substPreTermPlus (zip ys es) . snd) yts
  forM_ (zip ts ts') $ uncurry insConstraintEnv
  cod <- newTypeHoleInCtx (ctx ++ yts)
  insConstraintEnv univ $ typeOf cod
  let tPi = (metaTerminal, PreTermPi yts cod)
  insConstraintEnv tPi (typeOf e)
   -- cod' = ?M @ (ctx[0], ..., ctx[n], e1, ..., em)
  let cod' = substPreTermPlus (zip ys es) cod
  retPreTerm cod' (toLoc m) $ PreTermPiElim e es

-- In a context (x1 : A1, ..., xn : An), this function creates metavariables
--   ?M  : Pi (x1 : A1, ..., xn : An). ?Mt @ (x1, ..., xn)
--   ?Mt : Pi (x1 : A1, ..., xn : An). Univ
-- and return ?M @ (x1, ..., xn) : ?Mt @ (x1, ..., xn).
-- Note that we can't just set `?M : Pi (x1 : A1, ..., xn : An). Univ` since
-- WeakTermZeta might be used as an ordinary term, that is, a term which is not a type.
newHoleInCtx :: Context -> WithEnv PreTermPlus
newHoleInCtx ctx = do
  higherHole <- newHoleOfType (metaTerminal, PreTermPi ctx univ)
  varSeq <- mapM (uncurry toVar) ctx
  let app = (metaTerminal, PreTermPiElim higherHole varSeq)
  hole <- newHoleOfType (metaTerminal, PreTermPi ctx app)
  return (PreMetaNonTerminal app Nothing, PreTermPiElim hole varSeq)

-- In a context (x1 : A1, ..., xn : An), this function creates a metavariable
--   ?M  : Pi (x1 : A1, ..., xn : An). Univ
-- and return ?M @ (x1, ..., xn) : Univ.
newTypeHoleInCtx :: Context -> WithEnv PreTermPlus
newTypeHoleInCtx ctx = do
  varSeq <- mapM (uncurry toVar) ctx
  hole <- newHoleOfType (metaTerminal, PreTermPi ctx univ)
  return (PreMetaNonTerminal univ Nothing, PreTermPiElim hole varSeq)

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
     Context -> [Identifier] -> WithEnv [(Identifier, PreTermPlus)]
newTypeHoleListInCtx _ [] = return []
newTypeHoleListInCtx ctx (x:rest) = do
  t <- newTypeHoleInCtx ctx
  insWeakTypeEnv x t
  ts <- newTypeHoleListInCtx (ctx ++ [(x, t)]) rest
  return $ (x, t) : ts

inferCase :: Case -> WithEnv (Maybe PreTermPlus)
inferCase (CaseValue (EnumValueLabel name)) = do
  ienv <- gets enumEnv
  k <- lookupKind' name ienv
  return $ Just (metaTerminal, PreTermEnum $ EnumTypeLabel k)
inferCase (CaseValue (EnumValueNatNum i _)) =
  return $ Just (metaTerminal, PreTermEnum $ EnumTypeNatNum i)
inferCase _ = return Nothing

constrainList :: [PreTermPlus] -> WithEnv ()
constrainList [] = return ()
constrainList [_] = return ()
constrainList (t1:t2:ts) = do
  insConstraintEnv t1 t2
  constrainList $ t2 : ts

toVar :: Identifier -> PreTermPlus -> WithEnv PreTermPlus
toVar x t = do
  insWeakTypeEnv x t
  return (PreMetaNonTerminal t Nothing, PreTermUpsilon x)

retPreTerm :: PreTermPlus -> Maybe Loc -> PreTerm -> WithEnv PreTermPlus
retPreTerm t ml e = return (PreMetaNonTerminal t ml, e)

-- is-enum n{i}
toIsEnumType :: Integer -> WithEnv PreTermPlus
toIsEnumType i = do
  piType <- univToUniv
  let piMeta = PreMetaNonTerminal piType Nothing
  return
    ( metaTerminal
    , PreTermPiElim
        (piMeta, PreTermTheta "is-enum")
        [(metaTerminal, PreTermEnum $ EnumTypeNatNum i)])

-- Univ -> Univ
univToUniv :: WithEnv PreTermPlus
univToUniv = do
  h <- newNameWith "hole-univ-to-univ"
  return (metaTerminal, PreTermPi [(h, univ)] univ)

toLoc :: WeakMeta -> Maybe Loc
toLoc (WeakMetaTerminal ml) = ml
toLoc (WeakMetaNonTerminal ml) = ml

metaTerminal :: PreMeta
metaTerminal = PreMetaTerminal Nothing

newHoleOfType :: PreTermPlus -> WithEnv PreTermPlus
newHoleOfType t = do
  h <- newNameWith "hole-with-type"
  return (PreMetaNonTerminal t Nothing, PreTermZeta h)

determineDomType :: [PreTermPlus] -> PreTermPlus
determineDomType ts =
  if not (null ts)
    then head ts
    else (metaTerminal, PreTermTheta "bottom")
