module Elaborate.Infer
  ( infer
  , readWeakMetaType
  , typeOf
  , univ
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.IORef
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
infer _ (m, WeakTermTheta x)
  | Just i <- asEnumNatNumConstant x = do
    t <- toIsEnumType $ fromInteger i
    retPreTerm t (toLoc m) $ PreTermTheta x
  | otherwise = do
    mt <- lookupTypeEnvMaybe x
    case mt of
      Just t -> retPreTerm t (toLoc m) $ PreTermTheta x
      Nothing -> do
        h <- newHoleInCtx []
        insTypeEnv x h
        retPreTerm h (toLoc m) $ PreTermTheta x
infer _ (m, WeakTermUpsilon x) = do
  t <- lookupTypeEnv x
  retPreTerm t (toLoc m) $ PreTermUpsilon x
infer ctx (m, WeakTermPi xts t) = do
  (xts', t') <- inferPi ctx xts t
  retPreTerm univ (toLoc m) $ PreTermPi xts' t'
infer ctx (m, WeakTermPiIntro xts e) = do
  (xts', e') <- inferPiIntro ctx xts e
  let piType = (newMetaTerminal, PreTermPi xts' (typeOf e'))
  retPreTerm piType (toLoc m) $ PreTermPiIntro xts' e'
infer ctx (m, WeakTermPiElim e es) = do
  e' <- infer ctx e
  -- -- xts == [(x1, e1, t1), ..., (xn, en, tn)] with xi : ti and ei : ti
  (xs, es', ts) <- unzip3 <$> inferList ctx es
  let xts = zip xs ts
  -- cod = ?M @ ctx @ (x1, ..., xn)
  cod <- newHoleInCtx (ctx ++ xts)
  let tPi = (newMetaTerminal, PreTermPi xts cod)
  insConstraintEnv tPi (typeOf e')
  -- cod' = ?M @ ctx @ (e1, ..., en)
  let cod' = substPreTermPlus (zip xs es') cod
  retPreTerm cod' (toLoc m) $ PreTermPiElim e' es'
infer _ _ = undefined

-- infer ctx (meta, WeakTermPiIntro xts e) = inferPiIntro ctx meta xts e
-- infer ctx (meta, WeakTermPiElim e es) = do
--   tPi <- infer ctx e
--   -- xts == [(x1, t1), ..., (xn, tn)] with xi : ti and ei : ti
--   xts <- inferList ctx es
--   -- p "extendeding context by:"
--   -- p' xts
--   -- cod = ?M @ ctx @ (x1, ..., xn)
--   cod <- newHoleInCtx (ctx ++ xts)
--   let tPi' = (newMetaTerminal, WeakTermPi xts cod)
--   insConstraintEnv tPi tPi'
--   -- cod' = ?M @ ctx @ (e1, ..., en)
--   cod' <- substWeakTermPlus (zip (map fst xts) es) cod
--   returnAfterUpdate meta cod'
-- infer ctx (meta, WeakTermMu (x, t) e) = do
--   _ <- inferType ctx t
--   insTypeEnv x t
--   te <- infer (ctx ++ [(x, t)]) e
--   insConstraintEnv te t
--   returnAfterUpdate meta te
-- infer ctx (meta, WeakTermZeta x) = do
--   mt <- lookupTypeEnvMaybe x
--   case mt of
--     Just t
--       -- p "writing type:"
--       -- p' t
--      -> do
--       returnAfterUpdate meta t
--     Nothing -> do
--       h <- newHoleInCtx ctx
--       insTypeEnv x h
--       -- p "writing type:"
--       -- p' h
--       returnAfterUpdate meta h
-- infer _ (meta, WeakTermIntS size _) = do
--   returnAfterUpdate meta (newMetaTerminal, WeakTermTheta $ "i" ++ show size)
-- infer _ (meta, WeakTermIntU size _) = do
--   returnAfterUpdate meta (newMetaTerminal, WeakTermTheta $ "u" ++ show size)
-- infer _ (meta, WeakTermInt _) = do
--   h <- newHoleInCtx []
--   returnAfterUpdate meta h
-- infer _ (meta, WeakTermFloat16 _) =
--   returnAfterUpdate meta (newMetaTerminal, WeakTermTheta "f16")
-- infer _ (meta, WeakTermFloat32 _) =
--   returnAfterUpdate meta (newMetaTerminal, WeakTermTheta "f32")
-- infer _ (meta, WeakTermFloat64 _) =
--   returnAfterUpdate meta (newMetaTerminal, WeakTermTheta "f64")
-- infer _ (meta, WeakTermFloat _) = do
--   h <- newHoleInCtx []
--   returnAfterUpdate meta h -- f64 or "any float"
-- infer _ (meta, WeakTermEnum _) = returnAfterUpdate meta univ
-- infer _ (meta, WeakTermEnumIntro labelOrNum) = do
--   case labelOrNum of
--     EnumValueLabel l -> do
--       k <- lookupKind l
--       returnAfterUpdate meta (newMetaTerminal, WeakTermEnum $ EnumTypeLabel k)
--     EnumValueNatNum i _ ->
--       returnAfterUpdate meta (newMetaTerminal, WeakTermEnum $ EnumTypeNatNum i)
-- infer ctx (meta, WeakTermEnumElim e branchList) = do
--   te <- infer ctx e
--   if null branchList
--     then newHoleInCtx ctx >>= returnAfterUpdate meta -- ex falso quodlibet
--     else do
--       let (ls, es) = unzip branchList
--       tls <- mapM inferCase ls
--       constrainList $ te : catMaybes tls
--       ts <- mapM (infer ctx) es
--       constrainList ts
--       returnAfterUpdate meta $ head ts
-- infer ctx (meta, WeakTermArray _ from to) = do
--   uDom <- inferType ctx from
--   uCod <- inferType ctx to
--   insConstraintEnv uDom uCod
--   returnAfterUpdate meta uDom
-- infer ctx (meta, WeakTermArrayIntro kind les) = do
--   tCod <- inferKind kind
--   let (ls, es) = unzip les
--   tls <- mapM (inferCase . CaseValue) ls
--   constrainList $ catMaybes tls
--   ts <- mapM (infer ctx) es
--   constrainList $ tCod : ts
--   returnAfterUpdate meta tCod
-- infer ctx (meta, WeakTermArrayElim kind e1 e2) = do
--   tCod <- inferKind kind
--   tDom <- infer ctx e2
--   tDomToCod <- infer ctx e1
--   insConstraintEnv tDomToCod (newMetaTerminal, WeakTermArray kind tDom tCod)
--   returnAfterUpdate meta tCod
inferType :: Context -> WeakTermPlus -> WithEnv PreTermPlus
inferType ctx t = do
  t' <- infer ctx t
  insConstraintEnv (typeOf t') univ
  return t'

-- inferKind :: ArrayKind -> WithEnv WeakTermPlus
-- inferKind (ArrayKindIntS i) =
--   return (newMetaTerminal, WeakTermTheta $ "i" ++ show i)
-- inferKind (ArrayKindIntU i) =
--   return (newMetaTerminal, WeakTermTheta $ "u" ++ show i)
-- inferKind (ArrayKindFloat size) =
--   return (newMetaTerminal, WeakTermTheta $ "f" ++ show (sizeAsInt size))
-- inferPiIntro ::
--      Context -> WeakMeta -> Context -> WeakTermPlus -> WithEnv WeakTermPlus
-- inferPiIntro ctx meta xts e = inferPiIntro' ctx meta xts xts e
-- inferPiIntro' ::
--      Context
--   -> WeakMeta
--   -> [(Identifier, WeakTermPlus)]
--   -> Context
--   -> WeakTermPlus
--   -> WithEnv WeakTermPlus
-- inferPiIntro' ctx meta [] zts e = do
--   cod <- infer ctx e
--   undefined
--   -- returnAfterUpdate meta (newMetaTerminal, WeakTermPi zts cod)
-- inferPiIntro' ctx meta ((x, t):xts) zts e = do
--   t' <- inferType ctx t
--   insTypeEnv x t'
--   inferPiIntro' (ctx ++ [(x, t')]) meta xts zts e
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
  insTypeEnv x t'
  (xts', cod') <- inferPi (ctx ++ [(x, t')]) xts cod
  return ((x, t') : xts', cod')

inferPiIntro ::
     Context
  -> [(Identifier, WeakTermPlus)]
  -> WeakTermPlus
  -> WithEnv ([(Identifier, PreTermPlus)], PreTermPlus)
inferPiIntro ctx [] cod = do
  cod' <- infer ctx cod
  return ([], cod')
inferPiIntro ctx ((x, t):xts) cod = do
  t' <- infer ctx t
  insTypeEnv x t'
  (xts', cod') <- inferPiIntro (ctx ++ [(x, t')]) xts cod
  return ((x, t') : xts', cod')

newHoleInCtx :: Context -> WithEnv PreTermPlus
newHoleInCtx ctx = do
  higherHole <- newHoleOfType (newMetaTerminal, PreTermPi ctx univ)
  varSeq <- mapM (uncurry toVar) ctx
  let app = (newMetaTerminal, PreTermPiElim higherHole varSeq)
  hole <- newHoleOfType (newMetaTerminal, PreTermPi ctx app)
  return (PreMetaNonTerminal app Nothing, PreTermPiElim hole varSeq)
  -- wrapWithType app (WeakTermPiElim hole varSeq)
  -- higherHole <- newHoleOfType (newMetaTerminal, WeakTermPi ctx univ)
  -- varSeq <- mapM (uncurry toVar) ctx
  -- let app = (newMetaTerminal, WeakTermPiElim higherHole varSeq)
  -- hole <- newHoleOfType (newMetaTerminal, WeakTermPi ctx app)
  -- wrapWithType app (WeakTermPiElim hole varSeq)

-- inferCase :: Case -> WithEnv (Maybe WeakTermPlus)
-- inferCase (CaseValue (EnumValueLabel name)) = do
--   ienv <- gets enumEnv
--   k <- lookupKind' name ienv
--   return $ Just (newMetaTerminal, WeakTermEnum $ EnumTypeLabel k)
-- inferCase (CaseValue (EnumValueNatNum i _)) =
--   return $ Just (newMetaTerminal, WeakTermEnum $ EnumTypeNatNum i)
-- inferCase _ = return Nothing
--    inferList ctx [e1, ..., en]
-- ~> [(x1, t1), ..., (xn, tn)] with xi : ti, ei : ti
inferList ::
     Context
  -> [WeakTermPlus]
  -> WithEnv [(Identifier, PreTermPlus, PreTermPlus)]
inferList _ [] = return []
inferList ctx (e:es) = do
  e' <- infer ctx e
  x <- newNameWith "hole"
  -- _ <- inferType ctx t
  insTypeEnv x (typeOf e')
  xets <- inferList (ctx ++ [(x, (typeOf e'))]) es
  return $ (x, e', typeOf e') : xets

constrainList :: [PreTermPlus] -> WithEnv ()
constrainList [] = return ()
constrainList [_] = return ()
constrainList (t1:t2:ts) = do
  insConstraintEnv t1 t2
  constrainList $ t2 : ts

toVar :: Identifier -> PreTermPlus -> WithEnv PreTermPlus
toVar x t = do
  insTypeEnv x t
  return (PreMetaNonTerminal t Nothing, PreTermUpsilon x)

retPreTerm :: PreTermPlus -> Maybe Loc -> PreTerm -> WithEnv PreTermPlus
retPreTerm t ml e = return (PreMetaNonTerminal t ml, e)

-- returnAfterUpdate :: WeakMeta -> WeakTermPlus -> WithEnv WeakTermPlus
-- returnAfterUpdate m t = do
--   typeOrRef <- readWeakMetaType m
--   case typeOrRef of
--     Just t' -> insConstraintEnv t t'
--     Left r -> writeWeakTermRef r t
--   return t
univ :: PreTermPlus
univ = (PreMetaTerminal Nothing, PreTermTau)

-- wrapWithType :: WeakTermPlus -> WeakTerm -> WithEnv WeakTermPlus
-- wrapWithType t e = do
--   m <- newMetaOfType t
--   return (m, e)
readWeakMetaType :: WeakMeta -> WithEnv (Maybe PreTermPlus)
readWeakMetaType (WeakMetaTerminal _) = return $ Just univ
readWeakMetaType (WeakMetaNonTerminal _) = return Nothing

-- readWeakMetaType (WeakMetaTerminal _) = return $ Right univ
-- readWeakMetaType (WeakMetaNonTerminal r@(WeakTermRef ref) _) = do
--   mt <- liftIO $ readIORef ref
--   -- ここで仮にjustだったとしても、nonTerminalのなかにnonterminal nothingが入っている可能性がある、ということ？
--   case mt of
--     Just t -> return $ Right t
--     Nothing -> return $ Left r
typeOf :: PreTermPlus -> PreTermPlus
typeOf (PreMetaTerminal _, _) = univ
typeOf (PreMetaNonTerminal t _, _) = t

-- is-enum n{i}
toIsEnumType :: Int -> WithEnv PreTermPlus
toIsEnumType i = undefined
  -- piType <- univToUniv
  -- piMeta <- newMetaOfType piType
  -- return
  --   ( newMetaTerminal
  --   , WeakTermPiElim
  --       (piMeta, WeakTermTheta "is-enum")
  --       [(newMetaTerminal, WeakTermEnum $ EnumTypeNatNum i)])

-- Univ -> Univ
univToUniv :: WithEnv PreTermPlus
univToUniv = undefined
  -- h <- newNameWith "hole"
  -- return (newMetaTerminal, WeakTermPi [(h, univ)] univ)

toLoc :: WeakMeta -> Maybe Loc
toLoc (WeakMetaTerminal ml) = ml
toLoc (WeakMetaNonTerminal ml) = ml

newMetaTerminal :: PreMeta
newMetaTerminal = PreMetaTerminal Nothing

newHoleOfType :: PreTermPlus -> WithEnv PreTermPlus
newHoleOfType t = do
  h <- newNameWith "hole"
  return (PreMetaNonTerminal t Nothing, PreTermZeta h)
