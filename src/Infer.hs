module Infer
  ( check
  , unify
  ) where

import           Control.Monad
import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Control.Comonad.Cofree

import qualified Text.Show.Pretty           as Pr

import           Data

check :: Identifier -> Term -> WithEnv ()
check main e = do
  t <- infer e
  insTypeEnv main t -- insert the type of main function
  env <- get
  sub <- unify $ constraintEnv env
  let tenv' = map (\(s, t) -> (s, sType sub t)) $ typeEnv env
  modify (\e -> e {typeEnv = tenv', constraintEnv = []})

infer :: Term -> WithEnv Type
infer (meta :< TermVar s) = do
  mt <- lookupTypeEnv s
  case mt of
    Just t -> return t
    Nothing -> do
      new <- TypeHole <$> newName
      insTypeEnv s $ meta :< new
      return $ meta :< new
infer (meta :< TermThunk e) = do
  t <- infer e
  let result = meta :< TypeDown t
  return result
infer (meta :< TermLam s e) = do
  (tdom, arg) <- inferArg s
  te <- infer e
  let result = meta :< TypeForall (arg, tdom) te
  return result
infer (meta :< TermApp e v) = do
  te@(funMeta :< _) <- infer e
  tv <- infer v
  i <- newName
  let result = meta :< TypeHole i
  j <- newName
  insConstraintEnv te (funMeta :< TypeForall (j, tv) result)
  return result
infer (meta :< TermLift v) = do
  tv <- infer v
  return $ meta :< TypeUp tv
infer (meta :< TermColift v) = do
  tv <- infer v
  return $ meta :< TypeDown tv
infer (meta :< TermUnthunk v) = do
  t@(metaT :< _) <- infer v
  i <- newName
  let result = meta :< TypeHole i
  insConstraintEnv t (metaT :< TypeDown result)
  return result
infer (meta :< TermMu s e) = do
  (trec, ident) <- inferArg s
  insTypeEnv ident trec
  te <- infer e
  insConstraintEnv (meta :< TypeDown te) trec
  return te
infer (meta :< TermCase vs vses) = do
  ts <- mapM infer vs
  let (vss, es) = unzip vses
  tvss <- mapM (mapM inferPat) vss
  forM_ tvss $ \tvs -> do
    forM_ (zip ts tvs) $ \(t1, t2) -> do insConstraintEnv t1 t2
  ans <- TypeHole <$> newName
  tes <- mapM (infer) es
  forM_ tes $ \te -> insConstraintEnv (meta :< ans) te
  return (meta :< ans)
infer t = error $ "Infer.infer: illegal argument: " ++ Pr.ppShow t

inferPat :: Pat -> WithEnv Type
inferPat (meta :< PatHole) = do
  t <- TypeHole <$> newName
  return $ meta :< t
inferPat (meta :< PatVar s) = do
  mt <- lookupTypeEnv s
  case mt of
    Just t -> do
      return t
    Nothing -> do
      new <- TypeHole <$> newName
      insTypeEnv s $ meta :< new
      return $ meta :< new
inferPat (Meta {ident = j} :< PatApp s vs) = do
  mt <- lookupVEnv s
  case mt of
    Nothing -> lift $ throwE $ "const " ++ s ++ " is not defined"
    Just (_, xts, t) -> do
      tvs <- mapM inferPat vs
      -- need to add explicit parametrization
      forM_ (zip xts tvs) $ \(xt, t2) -> insConstraintEnv (snd xt) t2
      insTypeEnv j t
      return t

inferArg :: Arg -> WithEnv (Type, Identifier)
inferArg (ArgIdent x) = do
  i <- newNameWith x
  t <- newName
  return (Meta {ident = i} :< TypeHole t, x)
inferArg (ArgLift arg) = do
  (t@(meta :< _), ident) <- inferArg arg
  return (meta :< TypeUp t, ident)
inferArg (ArgColift arg) = do
  (t@(meta :< _), ident) <- inferArg arg
  return (meta :< TypeDown t, ident)

type Subst = [(String, Type)]

type Constraint = [(Type, Type)]

unify :: Constraint -> WithEnv Subst
unify [] = return []
unify ((_ :< TypeHole s, t2):cs) = do
  sub <- unify (sConstraint [(s, t2)] cs)
  return $ compose sub [(s, t2)]
unify ((t1, _ :< TypeHole s):cs) = do
  sub <- unify (sConstraint [(s, t1)] cs)
  return $ compose sub [(s, t1)]
unify ((_ :< TypeVar s1, _ :< TypeVar s2):cs)
  | s1 == s2 = unify cs
unify ((_ :< TypeForall (_, tdom1) tcod1, _ :< TypeForall (_, tdom2) tcod2):cs) = do
  unify $ (tdom1, tdom2) : (tcod1, tcod2) : cs
unify ((_ :< TypeNode x ts1, _ :< TypeNode y ts2):cs)
  | x == y = unify $ (zip ts1 ts2) ++ cs
unify ((_ :< TypeUp t1, _ :< TypeUp t2):cs) = do
  unify $ (t1, t2) : cs
unify ((_ :< TypeDown t1, _ :< TypeDown t2):cs) = do
  unify $ (t1, t2) : cs
unify ((_ :< TypeUniv i, _ :< TypeUniv j):cs) = do
  insLEnv i j
  unify cs
unify ((t1, t2):_) =
  lift $
  throwE $
  "unification failed for:\n" ++ Pr.ppShow t1 ++ "\nand:\n" ++ Pr.ppShow t2

compose :: Subst -> Subst -> Subst
compose s1 s2 = do
  let domS2 = map fst s2
  let codS2 = map snd s2
  let codS2' = map (sType s1) codS2
  let fromS1 = filter (\(ident, _) -> ident `notElem` domS2) s1
  fromS1 ++ zip domS2 codS2'

sType :: Subst -> Type -> Type
sType _ (meta :< TypeVar s) = meta :< TypeVar s
sType sub (meta :< TypeHole s) =
  case lookup s sub of
    Nothing -> meta :< TypeHole s
    Just t  -> t
sType sub (meta :< TypeUp t) = do
  let t' = sType sub t
  meta :< TypeUp t'
sType sub (meta :< TypeDown t) = do
  let t' = sType sub t
  meta :< TypeDown t'
sType _ (meta :< TypeUniv i) = meta :< TypeUniv i
sType sub (meta :< TypeForall (s, tdom) tcod) = do
  let tdom' = sType sub tdom
  let tcod' = sType sub tcod
  meta :< TypeForall (s, tdom') tcod'
sType sub (meta :< TypeNode s ts) = do
  let ts' = map (sType sub) ts
  meta :< TypeNode s ts'

sConstraint :: Subst -> Constraint -> Constraint
sConstraint s = map (\(t1, t2) -> (sType s t1, sType s t2))
