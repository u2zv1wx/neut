module Elaborate.Infer
  ( infer
  ) where

import           Control.Comonad.Cofree
import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.Maybe                 (maybeToList)
import qualified Text.Show.Pretty           as Pr

import           Data.Basic
import           Data.Env
import           Data.WeakTerm
import           Reduce.WeakTerm

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
-- In other words, when we generate a metavariable, we use `?M @ x1 @ ... @ xn` as a
-- representation of the hole, where x1, ..., xn are the defined names, or the context.
-- With this design, we can handle dependence in a simple way. This design decision
-- is due to "Elaboration in Dependent Type Theory". There also exists an approach
-- that deals with this situation which uses so-called contextual modality.
-- Interested readers are referred to A. Abel and B. Pientka. "Higher-Order
-- Dynamic Pattern Unification for Dependent Types and Records". Typed Lambda
-- Calculi and Applications, 2011.
infer :: Context -> WeakTerm -> WithEnv WeakTerm
infer _ (meta :< WeakTermVar s) = do
  univ <- newUniv
  t <- lookupTypeEnv' s >>= annot univ
  returnMeta meta t
infer ctx (meta :< WeakTermConst s) = do
  higherUniv <- newUniv
  univ <- newUniv >>= annot higherUniv
  t <- lookupTypeEnv' s >>= annot univ
  insTypeEnv s t
  u <- infer ctx t >>= annot higherUniv
  insConstraintEnv univ u
  returnMeta meta t
infer ctx (meta :< WeakTermPi (s, tdom) tcod) = do
  insTypeEnv s tdom
  higherUniv <- newUniv
  univ <- newUniv >>= annot higherUniv
  udom <- infer ctx tdom >>= annot higherUniv
  ucod <- infer (ctx ++ [(s, tdom)]) tcod >>= annot higherUniv
  insConstraintEnv udom ucod
  insConstraintEnv udom univ
  returnMeta meta univ
infer ctx (meta :< WeakTermPiIntro (s, tdom) e) = do
  univ <- newUniv
  tdom' <- annot univ tdom
  insTypeEnv1 s tdom'
  let ctx' = ctx ++ [(s, tdom')]
  tcod <- infer ctx' e >>= annot univ
  typeMeta <- newName' "meta" univ
  returnMeta meta $ typeMeta :< WeakTermPi (s, tdom') tcod
infer ctx (meta :< WeakTermPiElim e1 e2) = do
  univ <- newUniv
  -- obtain the type of e1
  tPi <- infer ctx e1 >>= reduceWeakTerm -- forall (x : tdom). tcod
  -- infer the type of e2, and obtain (tdom, udom)
  tdom <- infer ctx e2 >>= annot univ
  case tPi of
    _ :< WeakTermPi (x, tdom') tcod' -> do
      _ <- insDef x e2
      insConstraintEnv tdom tdom'
      returnMeta meta $ substWeakTerm [(x, e2)] tcod'
    _ -> do
      x <- newNameOfType tdom
      -- represent tcod using hole
      tcod <- appCtx (ctx ++ [(x, tdom)]) >>= annot univ
      -- add a constraint regarding the Pi-type
      typeMeta <- newNameWith "meta"
      insTypeEnv typeMeta univ
      insConstraintEnv tPi (typeMeta :< WeakTermPi (x, tdom) tcod)
      returnMeta meta $ substWeakTerm [(x, e2)] tcod
infer _ (meta :< WeakTermSigma []) = do
  univ <- newUniv
  returnMeta meta univ
infer ctx (meta :< WeakTermSigma ((x, t):xts))
  -- FIXME: Sigma (x, t) eの議論に帰着してPiと処理を統一したほうがよい
 = do
  insTypeEnv x t
  higherUniv <- newUniv
  univ <- newUniv >>= annot higherUniv
  udom <- infer ctx t >>= annot higherUniv
  ucod <- infer (ctx ++ [(x, t)]) (meta :< WeakTermSigma xts) >>= annot higherUniv
  insConstraintEnv udom ucod
  insConstraintEnv udom univ
  returnMeta meta univ
infer ctx (meta :< WeakTermSigmaIntro es) = do
  univ <- newUniv
  ts <- mapM (infer ctx) es
  forM_ ts $ annot univ
  xs <- forM ts $ \t -> newName1 "sigma" t
  holeList <- sigmaHole ctx xs
  let holeList' = map (substWeakTerm (zip xs es)) holeList
  forM_ (zip holeList' ts) $ uncurry insConstraintEnv
  returnMeta meta $ meta :< WeakTermSigma (zip xs holeList')
infer ctx (meta :< WeakTermSigmaElim xs e1 e2) = do
  univ <- newUniv
  t1 <- infer ctx e1 >>= annot univ
  holeList <- sigmaHole ctx xs
  forM_ (zip xs holeList) $ uncurry insTypeEnv
  t2 <- infer ctx e2 >>= annot univ
  let binder = zip xs holeList
  sigmaMeta <- newNameWith "meta"
  let sigmaType = sigmaMeta :< WeakTermSigma binder
  _ <- annot univ sigmaType
  insConstraintEnv t1 sigmaType
  z <- newNameOfType t1
  pair <- constructPair (ctx ++ zip xs holeList) xs
  typeC <- appCtx (ctx ++ zip xs holeList ++ [(z, t1)])
  insConstraintEnv t2 (substWeakTerm [(z, pair)] typeC)
  returnMeta meta $ substWeakTerm [(z, e1)] typeC
infer _ (meta :< WeakTermIndex _) = newUniv >>= returnMeta meta
infer ctx (meta :< WeakTermIndexIntro l) = do
  mk <- lookupKind l
  case mk of
    Just k -> do
      indexMeta <- newNameWith "meta"
      u <- newUniv
      insTypeEnv indexMeta u
      returnMeta meta $ indexMeta :< WeakTermIndex k
    Nothing -> do
      hole <- appCtx ctx
      returnMeta meta hole
infer _ (_ :< WeakTermIndexElim _ []) = lift $ throwE "empty branch"
infer ctx (meta :< WeakTermIndexElim e branchList) = do
  t <- infer ctx e
  let (labelList, es) = unzip branchList
  tls <- mapM (inferIndex ctx) labelList
  let tls' = join $ map maybeToList tls
  constrainList $ t : tls'
  tes <- mapM (infer ctx) es
  constrainList tes
  returnMeta meta $ head tes
infer ctx (meta :< WeakTermMu s e) = do
  univ <- newUniv
  trec <- appCtx ctx >>= annot univ
  insTypeEnv s trec
  te <- infer (ctx ++ [(s, trec)]) e >>= annot univ
  insConstraintEnv te trec
  returnMeta meta te
infer _ (meta :< WeakTermUniv _) = newUniv >>= returnMeta meta
infer ctx (meta :< WeakTermHole _) = appCtx ctx >>= returnMeta meta

-- In context ctx == [y1, ..., yn], `sigmaHole ctx names-of-holes` generates the list of
-- holes [name-1 @ ctx, name-2 @ ctx @ name-1, ..., name-n @ ctx @ name-1 @ ... @ name-(n-1)].
-- sigmaHole :: Context -> [Identifier] -> WithEnv [WeakTerm]
-- sigmaHole ctx xs = forM (zip xs [0 ..]) $ \(_, i) -> sigmaHole' ctx xs i
sigmaHole :: Context -> [Identifier] -> WithEnv [WeakTerm]
sigmaHole _ [] = return []
sigmaHole ctx (x:rest) = do
  t <- appCtx ctx
  ts <- sigmaHole (ctx ++ [(x, t)]) rest
  return $ t : ts

inferIndex :: Context -> Index -> WithEnv (Maybe WeakTerm)
inferIndex ctx (IndexLabel name) = do
  ienv <- gets indexEnv
  mk <- lookupKind' name ienv
  case mk of
    Just k -> Just <$> wrapType (WeakTermIndex k)
    Nothing -> do
      t <- appCtx ctx
      insTypeEnv name t
      return $ Just t
inferIndex _ _ = return Nothing

constrainList :: [WeakTerm] -> WithEnv ()
constrainList [] = return ()
constrainList [_] = return ()
constrainList (t1@(meta1 :< _):t2@(meta2 :< _):ts) = do
  u <- newUniv
  insTypeEnv meta1 u
  insTypeEnv meta2 u
  insConstraintEnv t1 t2
  constrainList $ t2 : ts

annot :: WeakTerm -> WeakTerm -> WithEnv WeakTerm
annot t e@(meta :< _) = insTypeEnv meta t >> return e

constructPair :: Context -> [Identifier] -> WithEnv WeakTerm
constructPair ctx xs = do
  eMeta <- newName
  metaList <- mapM (const newName) xs
  let varList = map (\(m, x) -> m :< WeakTermVar x) $ zip metaList xs
  let pair = eMeta :< WeakTermSigmaIntro varList
  _ <- infer ctx pair
  return pair

newName' :: Identifier -> WeakTerm -> WithEnv Identifier
newName' name t = do
  i <- newNameWith name
  insTypeEnv i t
  return i

-- Given a context `ctx`, generate a type variable `?M` and return `?M @ ctx`, inserting
-- correct type information to the environment.
appCtx :: Context -> WithEnv WeakTerm
appCtx ctx = do
  univ <- newUniv
  higherArrowType <- withEnvFoldR WeakTermPi univ ctx
  higherHoleName <- newName' "ctx" higherArrowType
  higherMeta <- newName' "ctx" higherArrowType
  insTypeEnv higherMeta higherArrowType
  let higherHole = higherMeta :< WeakTermHole higherHoleName
  varSeq <- mapM (uncurry toVar1) ctx
  cod <- appFoldWithType higherHole varSeq
  arrowType <- withEnvFoldR WeakTermPi cod ctx
  holeName <- newName' "hole" arrowType
  meta <- newName' "meta" arrowType
  appFoldWithType (meta :< WeakTermHole holeName) varSeq

toVar1 :: Identifier -> WeakTerm -> WithEnv WeakTerm
toVar1 x t = do
  meta <- newNameWith "meta"
  insTypeEnv meta t
  return $ meta :< WeakTermVar x

returnMeta :: Identifier -> WeakTerm -> WithEnv WeakTerm
returnMeta meta t = do
  insTypeEnv meta t
  return t

appFoldWithType :: WeakTerm -> [WeakTerm] -> WithEnv WeakTerm
appFoldWithType e [] = return e
appFoldWithType e@(i :< _) (term:ts) = do
  t <- lookupTypeEnv' i
  case t of
    _ :< WeakTermPi _ tcod -> do
      meta <- newNameWith "meta"
      insTypeEnv meta tcod
      appFoldWithType (meta :< WeakTermPiElim e term) ts
    _ ->
      lift $ throwE $ "appfold. t:\n" ++ Pr.ppShow t ++ "\ne:\n" ++ Pr.ppShow e

newUniv :: WithEnv WeakTerm
newUniv = do
  univMeta <- newNameWith "meta"
  l <- newName
  return $ univMeta :< WeakTermUniv (UnivLevelHole l)
