module Elaborate.Infer
  ( infer
  , newUniv
  , readWeakMetaType
  , writeWeakMetaType
  ) where

import           Control.Monad.Except
import           Control.Monad.State
import           Data.IORef
import           Data.Maybe           (catMaybes)
import           Prelude              hiding (pi)

import           Data.Basic
import           Data.Env
import           Data.WeakTerm

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
infer _ (meta, WeakTermTau) =
  returnAfterUpdate meta (newMetaTerminal, WeakTermTau) -- univ : univ
infer _ (meta, WeakTermTheta x) = do
  h <- newHoleInCtx [] -- constants do not depend on their context
  insTypeEnv x h
  returnAfterUpdate meta h
infer _ (meta, WeakTermUpsilon x) = do
  t <- lookupTypeEnv x
  returnAfterUpdate meta t
infer _ (meta, WeakTermEpsilon _) = newUniv >>= returnAfterUpdate meta
infer ctx (meta, WeakTermEpsilonIntro l) = do
  mk <- lookupKind l
  case mk of
    Just k -> wrapInfer ctx (WeakTermEpsilon k) >>= returnAfterUpdate meta
    -- when l is numeric literal such as `1`, `-231`, etc.
    Nothing -> do
      u <- newUniv
      h <- newHoleOfType u
      returnAfterUpdate meta h
infer ctx (meta, WeakTermEpsilonElim (x, t) e branchList) = do
  te <- infer ctx e
  insTypeEnv x t
  insConstraintEnv t te
  if null branchList
    then newHoleInCtx ctx >>= returnAfterUpdate meta -- ex falso quodlibet
    else do
      let (caseList, es) = unzip branchList
      tls <- mapM inferCase caseList
      constrainList $ te : catMaybes tls
      ts <- mapM (infer $ ctx ++ [(x, t)]) es
      constrainList ts
      returnAfterUpdate meta $ substWeakTermPlus [(x, e)] $ head ts
infer ctx (meta, WeakTermPi xts) = inferPiOrSigma ctx meta xts
infer ctx (meta, WeakTermPiIntro xts e) = do
  forM_ xts $ uncurry insTypeEnv
  cod <- infer (ctx ++ xts) e >>= withHole
  wrapInfer ctx (WeakTermPi (xts ++ [cod])) >>= returnAfterUpdate meta
infer ctx (meta, WeakTermPiElim e es) = do
  tPi <- infer ctx e
  binder <- inferList ctx es
  cod <- newHoleInCtx (ctx ++ binder) >>= withHole
  tPi' <- wrapInfer ctx $ WeakTermPi (binder ++ [cod])
  insConstraintEnv tPi tPi'
  returnAfterUpdate meta $ substWeakTermPlus (zip (map fst binder) es) $ snd cod
infer ctx (meta, WeakTermSigma xts) = inferPiOrSigma ctx meta xts
infer ctx (meta, WeakTermSigmaIntro es) = do
  binder <- inferList ctx es
  returnAfterUpdate meta (meta, WeakTermSigma binder)
infer ctx (meta, WeakTermSigmaElim xts e1 e2) = do
  t1 <- infer ctx e1
  forM_ xts $ uncurry insTypeEnv
  varSeq <- mapM (uncurry toVar) xts
  binder <- inferList ctx varSeq
  sigmaType <- wrapInfer ctx $ WeakTermSigma binder
  insConstraintEnv t1 sigmaType
  z <- newNameOfType t1
  varTuple <- constructTuple (ctx ++ binder) (map fst binder)
  typeC <- newHoleInCtx (ctx ++ binder ++ [(z, t1)])
  t2 <- infer (ctx ++ binder) e2
  insConstraintEnv t2 (substWeakTermPlus [(z, varTuple)] typeC)
  returnAfterUpdate meta $ substWeakTermPlus [(z, e1)] typeC
infer ctx (meta, WeakTermMu (x, t) e) = do
  insTypeEnv x t
  te <- infer (ctx ++ [(x, t)]) e
  insConstraintEnv te t
  returnAfterUpdate meta te
infer ctx (meta, WeakTermZeta _) = do
  mt <- readWeakMetaType meta
  case mt of
    Just t  -> return t
    Nothing -> newHoleInCtx ctx >>= returnAfterUpdate meta

inferPiOrSigma ::
     Context -> WeakMeta -> [IdentifierPlus] -> WithEnv WeakTermPlus
inferPiOrSigma ctx meta xts = do
  univList <-
    forM (map (`take` xts) [1 .. length xts]) $ \zts ->
      infer (ctx ++ init zts) (snd $ last zts)
  univ <- newUniv
  constrainList $ univ : univList
  returnAfterUpdate meta univ

-- In a context (x1 : A1, ..., xn : An), this function creates metavariables
--   ?M  : Pi (x1 : A1, ..., xn : An). ?Mt @ (x1, ..., xn)
--   ?Mt : Pi (x1 : A1, ..., xn : An). Ui
-- and return ?M @ (x1, ..., xn) : ?Mt @ (x1, ..., xn).
-- Note that we can't just set `?M : Pi (x1 : A1, ..., xn : An). Ui` since
-- WeakTermZeta might be used as a term which is not a type.
newHoleInCtx :: Context -> WithEnv WeakTermPlus
newHoleInCtx ctx = do
  univPlus <- newUniv >>= withHole
  higherPi <- wrapInfer ctx $ WeakTermPi $ ctx ++ [univPlus]
  higherHole <- newHoleOfType higherPi
  varSeq <- mapM (uncurry toVar) ctx
  let univ = snd univPlus
  appPlus <- wrapWithType univ (WeakTermPiElim higherHole varSeq) >>= withHole
  pi <- wrapInfer ctx $ WeakTermPi $ ctx ++ [appPlus]
  hole <- newHoleOfType pi
  let app = snd appPlus
  wrapWithType app (WeakTermPiElim hole varSeq)

-- In context ctx == [x1, ..., xn], `newHoleListInCtx ctx names-of-holes` generates
-- the following list of holes:
--
--   [m1 @ ctx,
--    m2 @ ctx @ y1,
--    ...,
--    mn @ ctx @ y1 @ ... @ y{n-1}]
--
-- inserting type information `yi : mi @ ctx @ y1 @ ... @ y{i-1}`.
newHoleListInCtx :: Context -> [Identifier] -> WithEnv [WeakTermPlus]
newHoleListInCtx _ [] = return []
newHoleListInCtx ctx (x:rest) = do
  t <- newHoleInCtx ctx
  insTypeEnv x t
  ts <- newHoleListInCtx (ctx ++ [(x, t)]) rest
  return $ t : ts

withHole :: WeakTermPlus -> WithEnv IdentifierPlus
withHole t = do
  h <- newNameWith "hole"
  return (h, t)

inferCase :: Case -> WithEnv (Maybe WeakTermPlus)
inferCase (CaseLiteral (LiteralLabel name)) = do
  ienv <- gets epsilonEnv
  mk <- lookupKind' name ienv
  case mk of
    Just k  -> Just <$> wrapInfer [] (WeakTermEpsilon k)
    Nothing -> return Nothing
inferCase _ = return Nothing

inferList :: Context -> [WeakTermPlus] -> WithEnv Context
inferList ctx es = do
  xs <- mapM (const $ newNameWith "hole") es
  holeList <- newHoleListInCtx ctx xs
  let holeList' = map (substWeakTermPlus (zip xs es)) holeList
  ts <- mapM (infer ctx) es
  forM_ (zip holeList' ts) $ uncurry insConstraintEnv
  return $ zip xs holeList

constrainList :: [WeakTermPlus] -> WithEnv ()
constrainList [] = return ()
constrainList [_] = return ()
constrainList (t1:t2:ts) = do
  insConstraintEnv t1 t2
  constrainList $ t2 : ts

constructTuple :: Context -> [Identifier] -> WithEnv WeakTermPlus
constructTuple ctx xs = do
  varList <- mapM toVar' xs
  wrapInfer ctx $ WeakTermSigmaIntro varList

toVar :: Identifier -> WeakTermPlus -> WithEnv WeakTermPlus
toVar x t = do
  insTypeEnv x t
  wrapWithType t (WeakTermUpsilon x)

toVar' :: Identifier -> WithEnv WeakTermPlus
toVar' x = do
  t <- lookupTypeEnv x
  wrapWithType t (WeakTermUpsilon x)

returnAfterUpdate :: WeakMeta -> WeakTermPlus -> WithEnv WeakTermPlus
returnAfterUpdate m t = do
  mt <- readWeakMetaType m
  case mt of
    Nothing -> writeWeakMetaType m (Just t)
    Just t' -> insConstraintEnv t t'
  return t

-- `newUniv` returns an "inferred" universe.
newUniv :: WithEnv WeakTermPlus
newUniv = wrapInfer [] WeakTermTau

wrapInfer :: Context -> WeakTerm -> WithEnv WeakTermPlus
wrapInfer ctx t = do
  t' <- wrap t
  _ <- infer ctx t'
  return t'

wrapWithType :: WeakTermPlus -> WeakTerm -> WithEnv WeakTermPlus
wrapWithType t e = do
  m <- newMetaOfType t
  return (m, e)

readWeakMetaType :: WeakMeta -> WithEnv (Maybe WeakTermPlus)
readWeakMetaType (WeakMetaNonTerminal (Ref r) _) = liftIO $ readIORef r
readWeakMetaType (WeakMetaTerminal _)            = Just <$> newUniv

writeWeakMetaType :: WeakMeta -> Maybe WeakTermPlus -> WithEnv ()
writeWeakMetaType (WeakMetaNonTerminal (Ref r) _) mt = liftIO $ writeIORef r mt
writeWeakMetaType (WeakMetaTerminal _) mt =
  case mt of
    Nothing -> return ()
    Just t -> do
      u <- newUniv
      insConstraintEnv u t
