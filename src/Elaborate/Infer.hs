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

type Context = [(WeakTerm, Identifier)]

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
infer _ (meta :< WeakTermUniv _) = newUniv >>= returnMeta meta
infer _ (meta :< WeakTermUpsilon x) = do
  t <- lookupTypeEnv' x
  returnMeta meta t
infer _ (meta :< WeakTermEpsilon _) = newUniv >>= returnMeta meta
infer _ (meta :< WeakTermEpsilonIntro l) = do
  mk <- lookupKind l
  epsilonMeta <- newNameWith "meta"
  case mk of
    Just k ->
      returnMeta meta $ epsilonMeta :< WeakTermEpsilon (WeakEpsilonIdentifier k)
    Nothing -> do
      hole <- newNameWith "hole"
      returnMeta meta $ epsilonMeta :< WeakTermEpsilon (WeakEpsilonHole hole)
infer ctx (meta :< WeakTermEpsilonElim (t, x) e branchList) = do
  te <- infer ctx e
  insTypeEnv x t
  constrainEpsilon te
  insConstraintEnv t te
  if null branchList
    then newHole >>= returnMeta meta -- ex falso quodlibet
    else do
      let (caseList, es) = unzip branchList
      tls <- mapM inferCase caseList
      let tls' = join $ map maybeToList tls
      constrainList $ te : tls'
      ts <- mapM (infer $ ctx ++ [(t, x)]) es
      constrainList ts
      returnMeta meta $ substWeakTerm [(x, e)] $ head ts
infer ctx (meta :< WeakTermPi s txs) = inferPiOrSigma ctx meta s txs
infer ctx (meta :< WeakTermPiIntro s txs e) = do
  infer ctx s >>= constrainEpsilon
  forM_ txs $ \(t, x) -> insTypeEnv x t
  cod <- infer (ctx ++ txs) e >>= withPlaceholder
  metaPi <- newNameWith "meta"
  returnMeta meta $ metaPi :< WeakTermPi s (txs ++ [cod])
infer ctx (meta :< WeakTermPiElim s e es) = do
  infer ctx s >>= constrainEpsilon
  tPi <- infer ctx e
  binder <- inferList ctx es
  cod <- newTypeVar (ctx ++ binder) >>= withPlaceholder
  metaPi <- newNameWith "meta"
  insConstraintEnv tPi (metaPi :< WeakTermPi s (binder ++ [cod]))
  returnMeta meta $ substWeakTerm (zip (map snd binder) es) $ fst cod
infer ctx (meta :< WeakTermSigma s txs) = inferPiOrSigma ctx meta s txs
infer ctx (meta :< WeakTermSigmaIntro s es) = do
  infer ctx s >>= constrainEpsilon
  binder <- inferList ctx es
  returnMeta meta $ meta :< WeakTermSigma s binder
infer ctx (meta :< WeakTermSigmaElim s txs e1 e2) = do
  infer ctx s >>= constrainEpsilon
  t1 <- infer ctx e1
  forM_ txs $ \(t, x) -> insTypeEnv x t
  varSeq <- mapM (uncurry toVar1) txs
  binder <- inferList ctx varSeq
  sigmaType <- wrapType $ WeakTermSigma s binder
  insConstraintEnv t1 sigmaType
  z <- newNameOfType t1
  varTuple <- constructTuple (ctx ++ binder) s (map snd binder)
  typeC <- newTypeVar (ctx ++ binder ++ [(t1, z)])
  t2 <- infer (ctx ++ binder) e2
  insConstraintEnv t2 (substWeakTerm [(z, varTuple)] typeC)
  returnMeta meta $ substWeakTerm [(z, e1)] typeC
infer ctx (meta :< WeakTermRec (t, x) e) = do
  insTypeEnv x t
  te <- infer (ctx ++ [(t, x)]) e
  insConstraintEnv te t
  returnMeta meta te
infer _ (meta :< WeakTermConst x) = do
  h <- newHole -- constants do not depend on their context
  insTypeEnv x h
  returnMeta meta h
infer ctx (meta :< WeakTermHole _) = newTypeVar ctx >>= returnMeta meta

inferPiOrSigma ::
     Context -> Identifier -> WeakTerm -> [IdentifierPlus] -> WithEnv WeakTerm
inferPiOrSigma ctx meta s txs = do
  infer ctx s >>= constrainEpsilon
  univList <-
    forM (map (`take` txs) [1 .. length txs]) $ \zts ->
      infer (ctx ++ init zts) (fst $ last zts)
  univ <- newUniv
  constrainList $ univ : univList
  returnMeta meta univ

-- In a context (x1 : A1, ..., xn : An), this function creates a metavariable
--   ?M : Pi (x1 : A1, ..., xn : An). Ui
-- and return ?M @ (x1, ..., xn) : Ui.
newTypeVar :: Context -> WithEnv WeakTerm
newTypeVar ctx = do
  univ <- newUniv >>= withPlaceholder
  s <- newCartesian
  pi <- wrapType $ WeakTermPi s $ ctx ++ [univ]
  hole <- newHoleOfType pi
  varSeq <- mapM (uncurry toVar1) ctx
  wrapType $ WeakTermPiElim s hole varSeq

-- In context ctx == [x1, ..., xn], `newTypeVarList ctx names-of-holes` generates
-- the following list of holes:
--
--   [m1 @ ctx,
--    m2 @ ctx @ y1,
--    ...,
--    mn @ ctx @ y1 @ ... @ y{n-1}]
--
-- inserting type information `yi : mi @ ctx @ y1 @ ... @ y{i-1}`.
newTypeVarList :: Context -> [Identifier] -> WithEnv [WeakTerm]
newTypeVarList _ [] = return []
newTypeVarList ctx (x:rest) = do
  t <- newTypeVar ctx
  insTypeEnv x t
  ts <- newTypeVarList (ctx ++ [(t, x)]) rest
  return $ t : ts

withPlaceholder :: WeakTerm -> WithEnv IdentifierPlus
withPlaceholder t = do
  h <- newNameWith "hole"
  return (t, h)

inferCase :: Case -> WithEnv (Maybe WeakTerm)
inferCase (CaseLiteral (LiteralLabel name)) = do
  ienv <- gets indexEnv
  mk <- lookupKind' name ienv
  case mk of
    Just k -> Just <$> wrapType (WeakTermEpsilon $ WeakEpsilonIdentifier k)
    Nothing -> do
      hole <- newNameWith "hole"
      Just <$> wrapType (WeakTermEpsilon $ WeakEpsilonHole hole)
inferCase _ = return Nothing

constrainEpsilon :: WeakTerm -> WithEnv ()
constrainEpsilon t = do
  h <- newNameWith "hole"
  meta <- newNameWith "meta"
  insConstraintEnv t (meta :< WeakTermEpsilon (WeakEpsilonHole h))

inferList :: Context -> [WeakTerm] -> WithEnv Context
inferList ctx es = do
  xs <- mapM (const $ newNameWith "hole") es
  holeList <- newTypeVarList ctx xs
  let holeList' = map (substWeakTerm (zip xs es)) holeList
  ts <- mapM (infer ctx) es
  forM_ (zip holeList' ts) $ uncurry insConstraintEnv
  return $ zip holeList xs

constrainList :: [WeakTerm] -> WithEnv ()
constrainList [] = return ()
constrainList [_] = return ()
constrainList (t1@(meta1 :< _):t2@(meta2 :< _):ts) = do
  u <- newUniv
  insTypeEnv meta1 u
  insTypeEnv meta2 u
  insConstraintEnv t1 t2
  constrainList $ t2 : ts

constructTuple :: Context -> WeakSortal -> [Identifier] -> WithEnv WeakTerm
constructTuple ctx s xs = do
  eMeta <- newName
  metaList <- mapM (const newName) xs
  let varList = map (\(m, x) -> m :< WeakTermUpsilon x) $ zip metaList xs
  let pair = eMeta :< WeakTermSigmaIntro s varList
  _ <- infer ctx pair
  return pair

toVar1 :: WeakTerm -> Identifier -> WithEnv WeakTerm
toVar1 t x = do
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
  l <- newName
  return $ univMeta :< WeakTermUniv (UnivLevelHole l)
