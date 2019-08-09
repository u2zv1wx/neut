module Elaborate.Infer
  ( infer
  ) where

import           Control.Comonad.Cofree
import           Control.Monad.Except
import           Control.Monad.State
import           Data.Maybe             (maybeToList)
import           Prelude                hiding (pi)

import           Data.Basic
import           Data.Env
import           Data.WeakTerm

type Context = [(Identifier, WeakTerm)]

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
infer :: Context -> WeakTerm -> WithEnv WeakTerm
infer _ (meta :< WeakTermUniverse) = newUniv >>= returnMeta meta
infer _ (meta :< WeakTermUpsilon x) = do
  t <- lookupTypeEnv' x
  returnMeta meta t
infer _ (meta :< WeakTermEpsilon _) = newUniv >>= returnMeta meta
infer _ (meta :< WeakTermEpsilonIntro l) = do
  mk <- lookupKind l
  epsilonMeta <- newNameWith "meta"
  case mk of
    Just k -> returnMeta meta $ epsilonMeta :< WeakTermEpsilon k
    Nothing -> do
      h <- newHole
      returnMeta meta h
infer ctx (meta :< WeakTermEpsilonElim (x, t) e branchList) = do
  te <- infer ctx e
  insTypeEnv x t
  insConstraintEnv t te
  if null branchList
    then newHole >>= returnMeta meta -- ex falso quodlibet
    else do
      let (caseList, es) = unzip branchList
      tls <- mapM inferCase caseList
      let tls' = join $ map maybeToList tls
      constrainList $ te : tls'
      ts <- mapM (infer $ ctx ++ [(x, t)]) es
      constrainList ts
      returnMeta meta $ substWeakTerm [(x, e)] $ head ts
infer ctx (meta :< WeakTermPi xts) = inferPiOrSigma ctx meta xts
infer ctx (meta :< WeakTermPiIntro xts e) = do
  forM_ xts $ uncurry insTypeEnv
  cod <- infer (ctx ++ xts) e >>= withPlaceholder
  wrap (WeakTermPi (xts ++ [cod])) >>= returnMeta meta
infer ctx (meta :< WeakTermPiElim e es) = do
  tPi <- infer ctx e
  binder <- inferList ctx es
  cod <- newHoleInCtx (ctx ++ binder) >>= withPlaceholder
  metaPi <- newNameWith "meta"
  insConstraintEnv tPi (metaPi :< WeakTermPi (binder ++ [cod]))
  returnMeta meta $ substWeakTerm (zip (map fst binder) es) $ snd cod
infer ctx (meta :< WeakTermSigma xts) = inferPiOrSigma ctx meta xts
infer ctx (meta :< WeakTermSigmaIntro es) = do
  binder <- inferList ctx es
  returnMeta meta $ meta :< WeakTermSigma binder
infer ctx (meta :< WeakTermSigmaElim xts e1 e2) = do
  t1 <- infer ctx e1
  forM_ xts $ uncurry insTypeEnv
  varSeq <- mapM (uncurry toVar) xts
  binder <- inferList ctx varSeq
  sigmaType <- wrap $ WeakTermSigma binder
  insConstraintEnv t1 sigmaType
  z <- newNameOfType t1
  varTuple <- constructTuple (ctx ++ binder) (map fst binder)
  typeC <- newHoleInCtx (ctx ++ binder ++ [(z, t1)])
  t2 <- infer (ctx ++ binder) e2
  insConstraintEnv t2 (substWeakTerm [(z, varTuple)] typeC)
  returnMeta meta $ substWeakTerm [(z, e1)] typeC
infer ctx (meta :< WeakTermMu (x, t) e) = do
  insTypeEnv x t
  te <- infer (ctx ++ [(x, t)]) e
  insConstraintEnv te t
  returnMeta meta te
infer _ (meta :< WeakTermConst x) = do
  h <- newHole -- constants do not depend on their context
  insTypeEnv x h
  returnMeta meta h
infer ctx (meta :< WeakTermHole _) = newHoleInCtx ctx >>= returnMeta meta

inferPiOrSigma :: Context -> Identifier -> [IdentifierPlus] -> WithEnv WeakTerm
inferPiOrSigma ctx meta xts = do
  univList <-
    forM (map (`take` xts) [1 .. length xts]) $ \zts ->
      infer (ctx ++ init zts) (snd $ last zts)
  univ <- newUniv
  constrainList $ univ : univList
  returnMeta meta univ

-- In a context (x1 : A1, ..., xn : An), this function creates metavariables
--   ?M  : Pi (x1 : A1, ..., xn : An). ?Mt @ (x1, ..., xn)
--   ?Mt : Pi (x1 : A1, ..., xn : An). Ui
-- and return ?M @ (x1, ..., xn) : ?Mt @ (x1, ..., xn).
-- Note that we can't just set `?M : Pi (x1 : A1, ..., xn : An). Ui` since
-- WeakTermHole might be used as a term which is not a type.
newHoleInCtx :: Context -> WithEnv WeakTerm
newHoleInCtx ctx = do
  univ <- newUniv >>= withPlaceholder
  higherPi <- wrap $ WeakTermPi $ ctx ++ [univ]
  higherHole <- newHoleOfType higherPi
  varSeq <- mapM (uncurry toVar) ctx
  app <- wrap (WeakTermPiElim higherHole varSeq) >>= withPlaceholder
  pi <- wrap $ WeakTermPi $ ctx ++ [app]
  hole <- newHoleOfType pi
  wrap $ WeakTermPiElim hole varSeq

-- In context ctx == [x1, ..., xn], `newHoleListInCtx ctx names-of-holes` generates
-- the following list of holes:
--
--   [m1 @ ctx,
--    m2 @ ctx @ y1,
--    ...,
--    mn @ ctx @ y1 @ ... @ y{n-1}]
--
-- inserting type information `yi : mi @ ctx @ y1 @ ... @ y{i-1}`.
newHoleListInCtx :: Context -> [Identifier] -> WithEnv [WeakTerm]
newHoleListInCtx _ [] = return []
newHoleListInCtx ctx (x:rest) = do
  t <- newHoleInCtx ctx
  insTypeEnv x t
  ts <- newHoleListInCtx (ctx ++ [(x, t)]) rest
  return $ t : ts

withPlaceholder :: WeakTerm -> WithEnv IdentifierPlus
withPlaceholder t = do
  h <- newNameWith "hole"
  return (h, t)

inferCase :: Case -> WithEnv (Maybe WeakTerm)
inferCase (CaseLiteral (LiteralLabel name)) = do
  ienv <- gets indexEnv
  mk <- lookupKind' name ienv
  case mk of
    Just k  -> Just <$> wrap (WeakTermEpsilon k)
    Nothing -> return Nothing
inferCase _ = return Nothing

inferList :: Context -> [WeakTerm] -> WithEnv Context
inferList ctx es = do
  xs <- mapM (const $ newNameWith "hole") es
  holeList <- newHoleListInCtx ctx xs
  let holeList' = map (substWeakTerm (zip xs es)) holeList
  ts <- mapM (infer ctx) es
  forM_ (zip holeList' ts) $ uncurry insConstraintEnv
  return $ zip xs holeList

constrainList :: [WeakTerm] -> WithEnv ()
constrainList [] = return ()
constrainList [_] = return ()
constrainList (t1@(meta1 :< _):t2@(meta2 :< _):ts) = do
  u <- newUniv
  insTypeEnv meta1 u
  insTypeEnv meta2 u
  insConstraintEnv t1 t2
  constrainList $ t2 : ts

constructTuple :: Context -> [Identifier] -> WithEnv WeakTerm
constructTuple ctx xs = do
  eMeta <- newName
  metaList <- mapM (const newName) xs
  let varList = map (\(m, x) -> m :< WeakTermUpsilon x) $ zip metaList xs
  let pair = eMeta :< WeakTermSigmaIntro varList
  _ <- infer ctx pair
  return pair

toVar :: Identifier -> WeakTerm -> WithEnv WeakTerm
toVar x t = do
  meta <- newNameWith "meta"
  insTypeEnv meta t
  insTypeEnv x t
  return $ meta :< WeakTermUpsilon x

returnMeta :: Identifier -> WeakTerm -> WithEnv WeakTerm
returnMeta meta t = do
  insTypeEnv meta t
  return t

newUniv :: WithEnv WeakTerm
newUniv = do
  univMeta <- newNameWith "meta"
  return $ univMeta :< WeakTermUniverse
