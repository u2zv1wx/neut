module Elaborate.Infer
  ( infer
  , readWeakMetaType
  , obtainType
  , univ
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.IORef
import Data.Maybe (catMaybes)
import Prelude hiding (pi)

import Data.Basic
import Data.Env
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
infer :: Context -> WeakTermPlus -> WithEnv WeakTermPlus
infer _ (meta, WeakTermTau) = returnAfterUpdate meta univ -- univ : univ
infer _ (meta, WeakTermTheta x)
  | Just i <- asEnumNatNumConstant x = do
    t <- toIsEnumType $ fromInteger i
    returnAfterUpdate meta t -- enum.n{i} : is-enum n{i}
  | otherwise = do
    mt <- lookupTypeEnvMaybe x
    case mt of
      Just t -> returnAfterUpdate meta t
      Nothing -> do
        h <- newHoleInCtx [] -- constants do not depend on their context
        insTypeEnv x h -- これだとthetaは出現のたびに異なる型をもつことになってしまう。
        returnAfterUpdate meta h
infer _ (meta, WeakTermUpsilon x) = do
  t <- lookupTypeEnv x
  returnAfterUpdate meta t
infer ctx (meta, WeakTermPi xts t) = do
  us <- inferPi ctx xts t
  constrainList $ univ : us
  returnAfterUpdate meta univ
infer ctx (meta, WeakTermPiIntro xts e) = inferPiIntro ctx meta xts e
infer ctx (meta, WeakTermPiElim e es) = do
  tPi <- infer ctx e
  -- xts == [(x1, t1), ..., (xn, tn)] with xi : ti and ei : ti
  xts <- inferList ctx es
  -- cod = ?M @ ctx @ (x1, ..., xn)
  cod <- newHoleInCtx (ctx ++ xts)
  let tPi' = (newMetaTerminal, WeakTermPi xts cod)
  insConstraintEnv tPi tPi'
  -- cod' = ?M @ ctx @ (e1, ..., en)
  cod' <- substWeakTermPlus (zip (map fst xts) es) cod
  returnAfterUpdate meta cod'
infer ctx (meta, WeakTermMu (x, t) e) = do
  _ <- inferType ctx t
  insTypeEnv x t
  te <- infer (ctx ++ [(x, t)]) e
  insConstraintEnv te t
  returnAfterUpdate meta te
infer ctx (meta, WeakTermZeta _) = do
  newHoleInCtx ctx >>= returnAfterUpdate meta
infer _ (meta, WeakTermIntS size _) = do
  returnAfterUpdate meta (newMetaTerminal, WeakTermTheta $ "i" ++ show size)
infer _ (meta, WeakTermIntU size _) = do
  returnAfterUpdate meta (newMetaTerminal, WeakTermTheta $ "u" ++ show size)
infer _ (meta, WeakTermInt _) = do
  h <- newHoleInCtx []
  returnAfterUpdate meta h
infer _ (meta, WeakTermFloat16 _) =
  returnAfterUpdate meta (newMetaTerminal, WeakTermTheta "f16")
infer _ (meta, WeakTermFloat32 _) =
  returnAfterUpdate meta (newMetaTerminal, WeakTermTheta "f32")
infer _ (meta, WeakTermFloat64 _) =
  returnAfterUpdate meta (newMetaTerminal, WeakTermTheta "f64")
infer _ (meta, WeakTermFloat _) = do
  h <- newHoleInCtx []
  returnAfterUpdate meta h -- f64 or "any float"
infer _ (meta, WeakTermEnum _) = returnAfterUpdate meta univ
infer _ (meta, WeakTermEnumIntro labelOrNum) = do
  case labelOrNum of
    EnumValueLabel l -> do
      k <- lookupKind l
      returnAfterUpdate meta (newMetaTerminal, WeakTermEnum $ EnumTypeLabel k)
    EnumValueNatNum i _ ->
      returnAfterUpdate meta (newMetaTerminal, WeakTermEnum $ EnumTypeNatNum i)
infer ctx (meta, WeakTermEnumElim e branchList) = do
  te <- infer ctx e
  if null branchList
    then newHoleInCtx ctx >>= returnAfterUpdate meta -- ex falso quodlibet
    else do
      let (ls, es) = unzip branchList
      tls <- mapM inferCase ls
      constrainList $ te : catMaybes tls
      ts <- mapM (infer ctx) es
      constrainList ts
      returnAfterUpdate meta $ head ts
infer ctx (meta, WeakTermArray _ from to) = do
  uDom <- inferType ctx from
  uCod <- inferType ctx to
  insConstraintEnv uDom uCod
  returnAfterUpdate meta uDom
infer ctx (meta, WeakTermArrayIntro kind les) = do
  tCod <- inferKind kind
  let (ls, es) = unzip les
  tls <- mapM (inferCase . CaseValue) ls
  constrainList $ catMaybes tls
  ts <- mapM (infer ctx) es
  constrainList $ tCod : ts
  returnAfterUpdate meta tCod
infer ctx (meta, WeakTermArrayElim kind e1 e2) = do
  tCod <- inferKind kind
  tDom <- infer ctx e2
  tDomToCod <- infer ctx e1
  insConstraintEnv tDomToCod (newMetaTerminal, WeakTermArray kind tDom tCod)
  returnAfterUpdate meta tCod

inferType :: Context -> WeakTermPlus -> WithEnv WeakTermPlus
inferType ctx t = do
  u <- infer ctx t
  insConstraintEnv u univ
  return u

inferKind :: ArrayKind -> WithEnv WeakTermPlus
inferKind (ArrayKindIntS i) =
  return (newMetaTerminal, WeakTermTheta $ "i" ++ show i)
inferKind (ArrayKindIntU i) =
  return (newMetaTerminal, WeakTermTheta $ "u" ++ show i)
inferKind (ArrayKindFloat size) =
  return (newMetaTerminal, WeakTermTheta $ "f" ++ show (sizeAsInt size))

inferPiIntro ::
     Context -> WeakMeta -> Context -> WeakTermPlus -> WithEnv WeakTermPlus
inferPiIntro ctx meta xts e = inferPiIntro' ctx meta xts xts e

inferPiIntro' ::
     Context
  -> WeakMeta
  -> Context
  -> Context
  -> WeakTermPlus
  -> WithEnv WeakTermPlus
inferPiIntro' ctx meta [] zts e = do
  cod <- infer ctx e
  returnAfterUpdate meta (newMetaTerminal, WeakTermPi zts cod)
inferPiIntro' ctx meta ((x, t):xts) zts e = do
  _ <- inferType ctx t
  insTypeEnv x t
  inferPiIntro' (ctx ++ [(x, t)]) meta xts zts e

inferPi ::
     Context
  -> [(Identifier, WeakTermPlus)]
  -> WeakTermPlus
  -> WithEnv [WeakTermPlus]
inferPi ctx [] cod = do
  u <- inferType ctx cod
  return [u]
inferPi ctx ((x, t):xts) cod = do
  u <- inferType ctx t
  insTypeEnv x t
  us <- inferPi (ctx ++ [(x, t)]) xts cod
  return $ u : us

newHoleInCtx :: Context -> WithEnv WeakTermPlus
newHoleInCtx ctx = do
  higherHole <- newHoleOfType (newMetaTerminal, WeakTermPi ctx univ)
  varSeq <- mapM (uncurry toVar) ctx
  let app = (newMetaTerminal, WeakTermPiElim higherHole varSeq)
  hole <- newHoleOfType (newMetaTerminal, WeakTermPi ctx app)
  wrapWithType app (WeakTermPiElim hole varSeq)

inferCase :: Case -> WithEnv (Maybe WeakTermPlus)
inferCase (CaseValue (EnumValueLabel name)) = do
  ienv <- gets enumEnv
  k <- lookupKind' name ienv
  return $ Just (newMetaTerminal, WeakTermEnum $ EnumTypeLabel k)
inferCase (CaseValue (EnumValueNatNum i _)) =
  return $ Just (newMetaTerminal, WeakTermEnum $ EnumTypeNatNum i)
inferCase _ = return Nothing

--    inferList ctx [e1, ..., en]
-- ~> [(x1, t1), ..., (xn, tn)] with xi : ti, ei : ti
inferList :: Context -> [WeakTermPlus] -> WithEnv Context
inferList _ [] = return []
inferList ctx (e:es) = do
  t <- infer ctx e
  x <- newNameWith "hole"
  _ <- inferType ctx t
  insTypeEnv x t
  xts <- inferList (ctx ++ [(x, t)]) es
  return $ (x, t) : xts

constrainList :: [WeakTermPlus] -> WithEnv ()
constrainList [] = return ()
constrainList [_] = return ()
constrainList (t1:t2:ts) = do
  insConstraintEnv t1 t2
  constrainList $ t2 : ts

toVar :: Identifier -> WeakTermPlus -> WithEnv WeakTermPlus
toVar x t = do
  insTypeEnv x t
  wrapWithType t (WeakTermUpsilon x)

returnAfterUpdate :: WeakMeta -> WeakTermPlus -> WithEnv WeakTermPlus
returnAfterUpdate m t = do
  typeOrRef <- readWeakMetaType m
  case typeOrRef of
    Right t' -> insConstraintEnv t t'
    Left r -> writeWeakTermRef r t
  return t

univ :: WeakTermPlus
univ = (WeakMetaTerminal Nothing, WeakTermTau)

wrapWithType :: WeakTermPlus -> WeakTerm -> WithEnv WeakTermPlus
wrapWithType t e = do
  m <- newMetaOfType t
  return (m, e)

readWeakMetaType :: WeakMeta -> WithEnv (Either WeakTermRef WeakTermPlus)
readWeakMetaType (WeakMetaTerminal _) = return $ Right univ
readWeakMetaType (WeakMetaNonTerminal r@(WeakTermRef ref) _) = do
  mt <- liftIO $ readIORef ref
  case mt of
    Just t -> return $ Right t
    Nothing -> return $ Left r

obtainType :: WeakMeta -> WithEnv WeakTermPlus
obtainType (WeakMetaTerminal _) = return univ
obtainType (WeakMetaNonTerminal ref _) = readWeakTermRef ref

-- is-enum n{i}
toIsEnumType :: Int -> WithEnv WeakTermPlus
toIsEnumType i = do
  piType <- univToUniv
  piMeta <- newMetaOfType piType
  return
    ( newMetaTerminal
    , WeakTermPiElim
        (piMeta, WeakTermTheta "is-enum")
        [(newMetaTerminal, WeakTermEnum $ EnumTypeNatNum i)])

-- Univ -> Univ
univToUniv :: WithEnv WeakTermPlus
univToUniv = do
  h <- newNameWith "hole"
  return (newMetaTerminal, WeakTermPi [(h, univ)] univ)
