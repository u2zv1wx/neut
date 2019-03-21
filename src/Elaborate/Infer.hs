module Elaborate.Infer
  ( infer
  ) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Trans.Except

import Control.Comonad.Cofree

import qualified Text.Show.Pretty as Pr

import Data
import Elaborate.Analyze
import Reduce
import Util

import Data.List

import Data.Maybe

import qualified Data.PQueue.Min as Q

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
infer :: Context -> Neut -> WithEnv Neut
infer _ (meta :< NeutVar s) = do
  univ <- boxUniv
  t <- lookupTypeEnv' s >>= annot univ
  returnMeta meta t
infer ctx (meta :< NeutConst s) = do
  higherUniv <- boxUniv
  univ <- boxUniv >>= annot higherUniv
  t <- lookupTypeEnv' s >>= annot univ
  insTypeEnv s t
  u <- infer ctx t >>= annot higherUniv
  insConstraintEnv (map fst ctx) univ u higherUniv
  returnMeta meta t
infer ctx (meta :< NeutPi (s, tdom) tcod) = do
  insTypeEnv s tdom
  higherUniv <- boxUniv
  univ <- boxUniv >>= annot higherUniv
  udom <- infer ctx tdom >>= annot higherUniv
  ucod <- infer (ctx ++ [(s, tdom)]) tcod >>= annot higherUniv
  insConstraintEnv (map fst ctx ++ [s]) udom ucod higherUniv
  insConstraintEnv (map fst ctx) udom univ higherUniv
  returnMeta meta univ
infer ctx (meta :< NeutPiIntro (s, tdom) e) = do
  univ <- boxUniv
  tdom' <- annot univ tdom
  insTypeEnv1 (map fst ctx) univ s tdom'
  let ctx' = ctx ++ [(s, tdom')]
  tcod <- infer ctx' e >>= annot univ
  typeMeta <- newName' "meta" univ
  returnMeta meta $ typeMeta :< NeutPi (s, tdom') tcod
infer ctx (meta :< NeutPiElim e1 e2) = do
  univ <- boxUniv
  -- obtain the type of e1
  tPi <- infer ctx e1 >>= reduce -- forall (x : tdom). tcod
  -- infer the type of e2, and obtain (tdom, udom)
  tdom <- infer ctx e2 >>= annot univ
  case tPi of
    _ :< NeutPi (x, tdom') tcod' -> do
      _ <- insDef x e2
      insConstraintEnv (map fst ctx) tdom tdom' univ
      returnMeta meta $ subst [(x, e2)] tcod'
    _ -> do
      x <- newNameOfType tdom
      -- represent tcod using hole
      tcod <- appCtx (ctx ++ [(x, tdom)]) >>= annot univ
      -- add a constraint regarding the Pi-type
      typeMeta <- newNameWith "meta"
      insTypeEnv typeMeta univ
      insConstraintEnv
        (map fst ctx)
        tPi
        (typeMeta :< NeutPi (x, tdom) tcod)
        univ
      -- return the type of this elimination
      returnMeta meta $ subst [(x, e2)] tcod
infer _ (meta :< NeutSigma []) = do
  univ <- boxUniv
  returnMeta meta univ
infer ctx (meta :< NeutSigma ((x, t):xts)) = do
  insTypeEnv x t
  higherUniv <- boxUniv
  univ <- boxUniv >>= annot higherUniv
  udom <- infer ctx t >>= annot higherUniv
  ucod <- infer (ctx ++ [(x, t)]) (meta :< NeutSigma xts) >>= annot higherUniv
  insConstraintEnv (map fst ctx ++ [x]) udom ucod higherUniv
  insConstraintEnv (map fst ctx) udom univ higherUniv
  returnMeta meta univ
infer ctx (meta :< NeutSigmaIntro es) = do
  univ <- boxUniv
  ts <- mapM (infer ctx) es
  forM_ ts $ annot univ
  xs <- forM ts $ \t -> newName1 "sigma" t
  holeList <- sigmaHole ctx xs
  let holeList' = map (subst (zip xs es)) holeList
  forM_ (zip holeList' ts) $ \(h, t) -> insConstraintEnv (map fst ctx) h t univ
  returnMeta meta $ meta :< NeutSigma (zip xs holeList')
infer ctx (meta :< NeutSigmaElim e1 xs e2) = do
  univ <- boxUniv
  t1 <- infer ctx e1 >>= annot univ
  holeList <- sigmaHole ctx xs
  forM_ (zip xs holeList) $ uncurry insTypeEnv
  t2 <- infer ctx e2 >>= annot univ
  let binder = zip xs holeList
  sigmaMeta <- newNameWith "meta"
  let sigmaType = sigmaMeta :< NeutSigma binder
  annot univ sigmaType
  insConstraintEnv (map fst ctx) t1 sigmaType univ
  z <- newNameOfType t1
  pair <- constructPair (ctx ++ zip xs holeList) xs
  typeC <- appCtx (ctx ++ (zip xs holeList) ++ [(z, t1)])
  insConstraintEnv (map fst ctx) t2 (subst [(z, pair)] typeC) univ
  returnMeta meta $ subst [(z, e1)] typeC
infer _ (meta :< NeutIndex _) = boxUniv >>= returnMeta meta
infer ctx (meta :< NeutIndexIntro l) = do
  mk <- lookupKind l
  case mk of
    Just k -> do
      indexMeta <- newNameWith "meta"
      u <- boxUniv
      insTypeEnv indexMeta u
      returnMeta meta $ indexMeta :< NeutIndex k
    Nothing -> do
      hole <- appCtx ctx
      insNumConstraintEnv meta
      returnMeta meta hole
infer _ (_ :< NeutIndexElim _ []) = lift $ throwE "empty branch"
infer ctx (meta :< NeutIndexElim e branchList) = do
  t <- infer ctx e
  let (labelList, es) = unzip branchList
  tls <- mapM (inferIndex ctx) labelList
  let tls' = join $ map maybeToList tls
  constrainList ctx tls'
  headConstraint ctx t tls'
  tes <- mapM (infer ctx) es
  constrainList ctx tes
  returnMeta meta $ head tes
infer ctx (meta :< NeutMu s e) = do
  univ <- boxUniv
  trec <- appCtx ctx >>= annot univ
  insTypeEnv s trec
  te <- infer (ctx ++ [(s, trec)]) e >>= annot univ
  insConstraintEnv (map fst ctx) te trec univ
  returnMeta meta te
infer _ (meta :< NeutUniv _) = boxUniv >>= returnMeta meta
infer ctx (meta :< NeutHole _) = appCtx ctx >>= returnMeta meta

-- In context ctx == [y1, ..., yn], `sigmaHole ctx names-of-holes` generates the list of
-- holes [name-1 @ ctx, name-2 @ ctx @ name-1, ..., name-n @ ctx @ name-1 @ ... @ name-(n-1)].
-- sigmaHole :: Context -> [Identifier] -> WithEnv [Neut]
-- sigmaHole ctx xs = forM (zip xs [0 ..]) $ \(_, i) -> sigmaHole' ctx xs i
sigmaHole :: Context -> [Identifier] -> WithEnv [Neut]
sigmaHole _ [] = return []
sigmaHole ctx (x:rest) = do
  t <- appCtx ctx
  ts <- sigmaHole (ctx ++ [(x, t)]) rest
  return $ t : ts

inferIndex :: Context -> IndexOrVar -> WithEnv (Maybe Neut)
inferIndex ctx (Right x) = do
  t <- appCtx ctx
  insTypeEnv x t
  return $ Just t
inferIndex ctx (Left (IndexLabel name)) = do
  ienv <- gets indexEnv
  mk <- lookupKind' name ienv
  case mk of
    Just k -> Just <$> wrapType (NeutIndex k)
    Nothing -> do
      t <- appCtx ctx
      insTypeEnv name t
      return $ Just t
inferIndex _ _ = return Nothing

constrainList :: Context -> [Neut] -> WithEnv ()
constrainList _ [] = return ()
constrainList _ [_] = return ()
constrainList ctx (t1@(meta1 :< _):t2@(meta2 :< _):ts) = do
  u <- boxUniv
  insTypeEnv meta1 u
  insTypeEnv meta2 u
  insConstraintEnv (map fst ctx) t1 t2 u
  constrainList ctx $ t2 : ts

headConstraint :: Context -> Neut -> [Neut] -> WithEnv ()
headConstraint _ _ [] = return ()
headConstraint ctx t1@(meta1 :< _) (t2@(meta2 :< _):_) = do
  u <- boxUniv
  insTypeEnv meta1 u
  insTypeEnv meta2 u
  insConstraintEnv (map fst ctx) t1 t2 u

annot :: Neut -> Neut -> WithEnv Neut
annot t e@(meta :< _) = insTypeEnv meta t >> return e

constructPair :: Context -> [Identifier] -> WithEnv Neut
constructPair ctx xs = do
  eMeta <- newName
  metaList <- mapM (const newName) xs
  let varList = map (\(m, x) -> m :< NeutVar x) $ zip metaList xs
  let pair = eMeta :< NeutSigmaIntro varList
  _ <- infer ctx pair
  return pair

newName' :: Identifier -> Neut -> WithEnv Identifier
newName' name t = do
  i <- newNameWith name
  insTypeEnv i t
  return i

-- Given a context `ctx`, generate a type variable `?M` and return `?M @ ctx`, inserting
-- correct type information to the environment.
appCtx :: Context -> WithEnv Neut
appCtx ctx = do
  univ <- boxUniv
  higherArrowType <- foldMR NeutPi univ ctx
  higherHoleName <- newName' "ctx" higherArrowType
  higherMeta <- newName' "ctx" higherArrowType
  insTypeEnv higherMeta higherArrowType
  let higherHole = higherMeta :< NeutHole higherHoleName
  varSeq <- mapM (uncurry toVar1) ctx
  cod <- appFold higherHole varSeq
  arrowType <- foldMR NeutPi cod ctx
  holeName <- newName' "hole" arrowType
  meta <- newName' "meta" arrowType
  appFold (meta :< NeutHole holeName) varSeq

returnMeta :: Identifier -> Neut -> WithEnv Neut
returnMeta meta t = do
  insTypeEnv meta t
  return t
