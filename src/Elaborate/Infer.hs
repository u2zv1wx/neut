module Elaborate.Infer
  ( infer
  , readWeakMetaType
  , writeWeakMetaType
  , withHole
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
infer _ (meta, WeakTermTheta x) = do
  h <- newHoleInCtx [] -- constants do not depend on their context
  insTypeEnv x h
  returnAfterUpdate meta h
infer _ (meta, WeakTermUpsilon x) = do
  t <- lookupTypeEnv x
  returnAfterUpdate meta t
infer ctx (meta, WeakTermPi xts) = do
  univList <- inferPlus ctx xts
  constrainList $ univ : univList
  returnAfterUpdate meta univ
infer ctx (meta, WeakTermPiIntro xts e) = inferPiIntro ctx meta xts e
infer ctx (meta, WeakTermPiElim e es) = do
  tPi <- infer ctx e
  -- xts == [(x1, t1), ..., (xn, tn)] with xi : ti and ei : ti
  xts <- inferList ctx es
  -- codHole = ?M
  -- cod = ?M @ ctx @ x1 @ ... @ xn
  (codHole, cod) <- newHoleInCtx' (ctx ++ xts)
  h <- newNameWith "hole"
  let tPi' = (newMetaTerminal, WeakTermPi $ xts ++ [(h, cod)])
  insConstraintEnv tPi tPi'
  -- codAfterElim == ?M @ ctx @ e1 @ ... @ en
  codAfterElim <- newCtxAppHole ctx codHole es
  returnAfterUpdate meta codAfterElim
infer ctx (meta, WeakTermMu (x, t) e) = do
  inferType ctx t
  insTypeEnv x t
  te <- infer (ctx ++ [(x, t)]) e
  insConstraintEnv te t
  returnAfterUpdate meta te
infer ctx (meta, WeakTermZeta _) = do
  mt <- readWeakMetaType meta
  case mt of
    Just t -> return t
    Nothing -> newHoleInCtx ctx >>= returnAfterUpdate meta
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
infer _ (meta, WeakTermEnumIntro l) = do
  k <- lookupKind l
  returnAfterUpdate meta (newMetaTerminal, WeakTermEnum k)
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
  uDom <- infer ctx from
  uCod <- infer ctx to
  insConstraintEnv uDom uCod
  returnAfterUpdate meta uDom
infer ctx (meta, WeakTermArrayIntro kind les) = do
  tCod <- inferKind kind
  let (ls, es) = unzip les
  tls <- mapM (inferCase . CaseLabel) ls
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

inferType :: Context -> WeakTermPlus -> WithEnv ()
inferType ctx t = do
  u <- infer ctx t
  insConstraintEnv u univ

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
  (_, codPlus) <- infer ctx e >>= withHole
  returnAfterUpdate meta (newMetaTerminal, WeakTermPi $ zts ++ [codPlus])
inferPiIntro' ctx meta ((x, t):xts) zts e = do
  inferType ctx t
  insTypeEnv x t
  inferPiIntro' (ctx ++ [(x, t)]) meta xts zts e

inferPlus :: Context -> [(Identifier, WeakTermPlus)] -> WithEnv [WeakTermPlus]
inferPlus ctx xts =
  forM (map (`take` xts) [1 .. length xts]) $ \zts ->
    infer (ctx ++ init zts) (snd $ last zts)

-- In a context (x1 : A1, ..., xn : An), this function creates metavariables
--   ?M  : Pi (x1 : A1, ..., xn : An). ?Mt @ (x1, ..., xn) -- pi
--   ?Mt : Pi (x1 : A1, ..., xn : An). Univ                -- higherPi
-- and return ?M @ (x1, ..., xn) : ?Mt @ (x1, ..., xn).    -- ?Mt == higherHole
-- Note that we can't just set `?M : Pi (x1 : A1, ..., xn : An). Ui` since
-- WeakTermZeta might be used as a term which is not a type.
newHoleInCtx :: Context -> WithEnv WeakTermPlus
newHoleInCtx ctx = snd <$> newHoleInCtx' ctx

newHoleInCtx' :: Context -> WithEnv (WeakTermPlus, WeakTermPlus)
newHoleInCtx' ctx = do
  (_, univPlus) <- withHole univ
  let higherPi = (newMetaTerminal, WeakTermPi $ ctx ++ [univPlus])
  higherHole <- newHoleOfType higherPi
  varSeq <- mapM (uncurry toVar) ctx
  (_, appPlus) <- withHole (newMetaTerminal, WeakTermPiElim higherHole varSeq)
  let pi = (newMetaTerminal, WeakTermPi $ ctx ++ [appPlus])
  hole <- newHoleOfType pi
  newHoleInCtx'' ctx hole

newHoleInCtx'' ::
     Context -> WeakTermPlus -> WithEnv (WeakTermPlus, WeakTermPlus)
newHoleInCtx'' ctx hole = do
  (_, univPlus) <- withHole univ
  let higherPi = (newMetaTerminal, WeakTermPi $ ctx ++ [univPlus])
  higherHole <- newHoleOfType higherPi
  varSeq <- mapM (uncurry toVar) ctx
  (app, _) <- withHole (newMetaTerminal, WeakTermPiElim higherHole varSeq)
  app' <- wrapWithType app (WeakTermPiElim hole varSeq)
  return (hole, app')

--    newCtxAppHole ctx [e1, ..., en]
-- ~> ?M @ ctx @ e1 @ ... @ en
newCtxAppHole ::
     Context -> WeakTermPlus -> [WeakTermPlus] -> WithEnv WeakTermPlus
newCtxAppHole ctx hole es = do
  xs <- mapM (const $ newNameWith "arg") es
  (_, appHole) <- newHoleInCtx'' (ctx ++ zip xs es) hole
  return appHole

inferCase :: Case -> WithEnv (Maybe WeakTermPlus)
inferCase (CaseLabel name) = do
  ienv <- gets enumEnv
  k <- lookupKind' name ienv
  return $ Just (newMetaTerminal, WeakTermEnum k)
inferCase _ = return Nothing

--    inferList ctx [e1, ..., en]
-- ~> [(x1, t1), ..., (xn, tn)] with xi : ti, ei : ti
inferList :: Context -> [WeakTermPlus] -> WithEnv Context
inferList _ [] = return []
inferList ctx (e:es) = do
  t <- infer ctx e
  x <- newNameWith "hole"
  inferType ctx t
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
  mt <- readWeakMetaType m
  case mt of
    Nothing -> writeWeakMetaType m (Just t)
    Just t' -> insConstraintEnv t t'
  return t

univ :: WeakTermPlus
univ = (WeakMetaTerminal Nothing, WeakTermTau)

withHole :: WeakTermPlus -> WithEnv (WeakTermPlus, IdentifierPlus)
withHole t = do
  h <- newNameWith "hole"
  return (t, (h, t))

wrapWithType :: WeakTermPlus -> WeakTerm -> WithEnv WeakTermPlus
wrapWithType t e = do
  m <- newMetaOfType t
  return (m, e)

readWeakMetaType :: WeakMeta -> WithEnv (Maybe WeakTermPlus)
readWeakMetaType (WeakMetaNonTerminal (Ref r) _) = liftIO $ readIORef r
readWeakMetaType (WeakMetaTerminal _) = return $ Just univ

writeWeakMetaType :: WeakMeta -> Maybe WeakTermPlus -> WithEnv ()
writeWeakMetaType (WeakMetaNonTerminal (Ref r) _) mt = liftIO $ writeIORef r mt
writeWeakMetaType (WeakMetaTerminal _) mt =
  case mt of
    Nothing -> return ()
    Just t -> insConstraintEnv univ t
