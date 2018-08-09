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

check :: WeakTerm -> WithEnv ()
check e = do
  _ <- infer e
  env <- get
  sub <- unify $ constraintEnv env
  liftIO $ putStrLn $ Pr.ppShow sub
  env' <- get
  let aenv = argEnv env'
  argSubst <- unifyArg aenv
  let tenv' =
        map (\(s, t) -> (s, applyArgSubst argSubst $ sType sub t)) $
        weakTypeEnv env
  modify (\e -> e {weakTypeEnv = tenv', constraintEnv = []})

infer :: WeakTerm -> WithEnv WeakType
infer (Meta {ident = i} :< WeakTermVar s) = do
  mt <- lookupWTEnv s
  case mt of
    Just t -> do
      insWTEnv i t
      return t
    Nothing -> do
      new <- WeakTypeHole <$> newName
      insWTEnv s new
      insWTEnv i new
      return new
infer (Meta {ident = i} :< WeakTermConst s) = do
  mt <- lookupVEnv s
  case mt of
    Just t -> do
      let t' = weakenValueType t
      insWTEnv i t'
      return t'
    Nothing -> lift $ throwE $ "const " ++ s ++ " is not defined"
infer (Meta {ident = i} :< WeakTermLam (s, t) e) = do
  insWTEnv s t
  te <- infer e
  let result = WeakTypeForall (Ident s, t) te
  insWTEnv i result
  return result
infer (Meta {ident = j} :< WeakTermNodeApp s vs) = do
  mt <- lookupVEnv s
  case mt of
    Nothing -> undefined
    Just t -> do
      is <- forM vs $ \_ -> newName
      ts <- mapM infer vs
      i <- newName
      let t' = WeakTypeNode (zip is ts) (WeakTypeHole i)
      insCEnv (weakenValueType t) t'
      let result = WeakTypeHole i
      insWTEnv j result
      return result
infer (Meta {ident = l} :< WeakTermApp e v) = do
  te <- infer e
  tv <- infer v
  i <- newName
  insWTEnv i (WeakTypeHole i)
  j <- newName
  insCEnv te (WeakTypeForall (Hole j, tv) (WeakTypeHole i))
  let result = WeakTypeHole i
  insWTEnv l result
  return result
infer (Meta {ident = i} :< WeakTermRet v) = do
  tv <- infer v
  let result = WeakTypeUp tv
  insWTEnv i result
  return result
infer (Meta {ident = i} :< WeakTermBind (s, t) e1 e2) = do
  insWTEnv s t
  t1 <- infer e1
  t2 <- infer e2
  insCEnv (WeakTypeUp t) t1
  insWTEnv i t2
  return t2
infer (Meta {ident = i} :< WeakTermThunk e) = do
  t <- infer e
  let result = WeakTypeDown t i
  insWTEnv i result
  return result
infer (Meta {ident = l} :< WeakTermUnthunk v) = do
  t <- infer v
  i <- newName
  insCEnv t (WeakTypeDown (WeakTypeHole i) l)
  let result = WeakTypeHole i
  insWTEnv l result
  return result
infer (Meta {ident = i} :< WeakTermMu (s, t) e) = do
  insWTEnv s t
  te <- infer e
  insCEnv (WeakTypeDown te i) t
  insWTEnv i te
  return te
infer (Meta {ident = i} :< WeakTermCase e ves) = do
  t <- infer e
  let (vs, es) = unzip ves
  tvs <- mapM inferPat vs
  forM_ tvs $ \tv -> insCEnv t tv
  ans <- WeakTypeHole <$> newName
  tes <- mapM infer es
  forM_ tes $ \te -> insCEnv ans te
  insWTEnv i ans
  return ans
infer (Meta {ident = i} :< WeakTermAsc e t) = do
  te <- infer e
  insCEnv t te
  insWTEnv i te
  return te

inferPat :: Pat -> WithEnv WeakType
inferPat (Meta {ident = i} :< PatVar s) = do
  mt <- lookupWTEnv s
  case mt of
    Just t -> do
      insWTEnv i t
      return t
    Nothing -> do
      new <- WeakTypeHole <$> newName
      insWTEnv s new
      insWTEnv i new
      return new
inferPat (Meta {ident = i} :< PatConst s) = do
  mt <- lookupVEnv s
  case mt of
    Just t -> do
      let t' = weakenValueType t
      insWTEnv i t'
      return t'
    Nothing -> lift $ throwE $ "const " ++ s ++ " is not defined"
inferPat (Meta {ident = _} :< PatApp s vs) = do
  mt <- lookupVEnv s
  case mt of
    Nothing -> undefined
    Just t -> do
      is <- forM vs $ \_ -> newName
      ts <- mapM inferPat vs
      i <- newName
      let t' = WeakTypeNode (zip is ts) (WeakTypeHole i)
      insCEnv (weakenValueType t) t'
      return $ WeakTypeHole i

type Subst = [(String, WeakType)]

type Constraint = [(WeakType, WeakType)]

unify :: Constraint -> WithEnv Subst
unify [] = return []
unify ((WeakTypeHole s, t2):cs) = do
  sub <- unify (sConstraint [(s, t2)] cs)
  return $ compose sub [(s, t2)]
unify ((t1, WeakTypeHole s):cs) = do
  sub <- unify (sConstraint [(s, t1)] cs)
  return $ compose sub [(s, t1)]
unify ((WeakTypeVar s1, WeakTypeVar s2):cs)
  | s1 == s2 = unify cs
unify ((WeakTypeConst s1, WeakTypeConst s2):cs)
  | s1 == s2 = unify cs
unify ((WeakTypeForall (i, tdom1) tcod1, WeakTypeForall (j, tdom2) tcod2):cs) = do
  insAEnv i j
  unify $ (tdom1, tdom2) : (tcod1, tcod2) : cs
unify ((WeakTypeNode xts tcod1, WeakTypeNode yts tcod2):cs)
  | length xts == length yts =
    unify $ (tcod1, tcod2) : (zip (map snd xts) (map snd yts)) ++ cs
unify ((WeakTypeUp t1, WeakTypeUp t2):cs) = do
  unify $ (t1, t2) : cs
unify ((WeakTypeDown t1 i, WeakTypeDown t2 j):cs) = do
  insThunkEnv i j
  unify $ (t1, t2) : cs
unify ((WeakTypeUniv i, WeakTypeUniv j):cs) = do
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

sType :: Subst -> WeakType -> WeakType
sType _ (WeakTypeVar s) = WeakTypeVar s
sType sub (WeakTypeHole s) =
  case lookup s sub of
    Nothing -> WeakTypeHole s
    Just t  -> t
sType _ (WeakTypeConst s) = WeakTypeConst s
sType sub (WeakTypeUp t) = do
  let t' = sType sub t
  WeakTypeUp t'
sType sub (WeakTypeDown t i) = do
  let t' = sType sub t
  WeakTypeDown t' i
sType _ (WeakTypeUniv i) = WeakTypeUniv i
sType sub (WeakTypeForall (s, tdom) tcod) = do
  let tdom' = sType sub tdom
  let tcod' = sType sub tcod
  WeakTypeForall (s, tdom') tcod'
sType sub (WeakTypeNode xts tcod) = do
  let xts' = map (\(x, t) -> (x, sType sub t)) xts
  let tcod' = sType sub tcod
  WeakTypeNode xts' tcod'

sConstraint :: Subst -> Constraint -> Constraint
sConstraint s = map (\(t1, t2) -> (sType s t1, sType s t2))

type ArgConstraint = [(IdentOrHole, IdentOrHole)]

type ArgSubst = [(Identifier, IdentOrHole)]

unifyArg :: ArgConstraint -> WithEnv ArgSubst
unifyArg [] = return []
unifyArg ((Hole s1, j):cs) = do
  sub <- unifyArg (sArgConstraint [(s1, j)] cs)
  return $ argCompose sub [(s1, j)]
unifyArg ((i, Hole s2):cs) = do
  sub <- unifyArg (sArgConstraint [(s2, i)] cs)
  return $ argCompose sub [(s2, i)]
unifyArg ((Ident s1, Ident s2):cs)
  | s1 == s2 = unifyArg cs
unifyArg ((x, y):_) =
  lift $
  throwE $
  "arg-unification failed for:\n" ++ Pr.ppShow x ++ "\nand:\n" ++ Pr.ppShow y

sArgConstraint :: ArgSubst -> ArgConstraint -> ArgConstraint
sArgConstraint s = map (\(t1, t2) -> (sArg s t1, sArg s t2))

sArg :: ArgSubst -> IdentOrHole -> IdentOrHole
sArg cs (Ident s) =
  case lookup s cs of
    Nothing -> Ident s
    Just s' -> s'
sArg cs (Hole s) =
  case lookup s cs of
    Nothing -> Hole s
    Just s' -> s'

argCompose :: ArgSubst -> ArgSubst -> ArgSubst
argCompose s1 s2 = do
  let domS2 = map fst s2
  let codS2 = map snd s2
  let codS2' = map (sArg s1) codS2
  let fromS1 = filter (\(ident, _) -> ident `notElem` domS2) s1
  fromS1 ++ zip domS2 codS2'

applyArgSubst :: ArgSubst -> WeakType -> WeakType
applyArgSubst _ (WeakTypeVar s) = WeakTypeVar s
applyArgSubst _ (WeakTypeHole s) = WeakTypeHole s
applyArgSubst _ (WeakTypeConst s) = WeakTypeConst s
applyArgSubst sub (WeakTypeNode xts tcod) = do
  let (xs, ts) = unzip xts
  let ts' = map (applyArgSubst sub) ts
  let tcod' = applyArgSubst sub tcod
  WeakTypeNode (zip xs ts') tcod'
applyArgSubst sub (WeakTypeUp t) = do
  let t' = applyArgSubst sub t
  WeakTypeUp t'
applyArgSubst sub (WeakTypeDown t i) = do
  let t' = applyArgSubst sub t
  WeakTypeDown t' i
applyArgSubst _ (WeakTypeUniv i) = WeakTypeUniv i
applyArgSubst sub (WeakTypeForall (s, tdom) tcod) = do
  let tdom' = applyArgSubst sub tdom
  let tcod' = applyArgSubst sub tcod
  WeakTypeForall (sArg sub s, tdom') tcod'
