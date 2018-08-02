module Typing
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
  let tenv' = map (\(s, t) -> (s, sType sub t)) $ typeEnv env
  modify (\e -> e {typeEnv = tenv', constraintEnv = []})

infer :: WeakTerm -> WithEnv WeakType
infer (Meta {ident = i} :< WeakTermVar s) = do
  mt <- lookupTEnv s
  case mt of
    Just t -> do
      insTEnv i t
      return t
    Nothing -> do
      new <- WeakTypeHole <$> newName
      insTEnv s new
      insTEnv i new
      return new
infer (Meta {ident = i} :< WeakTermConst s) = do
  mt <- lookupVEnv s
  case mt of
    Just t -> do
      let t' = weakenValueType t
      insTEnv i t'
      return t'
    Nothing -> lift $ throwE $ "const " ++ s ++ " is not defined"
infer (Meta {ident = i} :< WeakTermLam (s, t) e) = do
  insTEnv s t
  te <- infer e
  let result = WeakTypeForall (s, t) te
  insTEnv i result
  return result
infer (Meta {ident = l} :< WeakTermApp e v) = do
  te <- infer e
  tv <- infer v
  i <- newName
  insTEnv i (WeakTypeHole i)
  j <- newName
  insTEnv j tv
  insCEnv te (WeakTypeForall (j, tv) (WeakTypeHole i))
  let result = WeakTypeHole i
  insTEnv l result
  return result
infer (Meta {ident = i} :< WeakTermRet v) = do
  tv <- infer v
  let result = WeakTypeUp tv
  insTEnv i result
  return result
infer (Meta {ident = i} :< WeakTermBind (s, t) e1 e2) = do
  insTEnv s t
  t1 <- infer e1
  t2 <- infer e2
  insCEnv (WeakTypeUp t) t1
  insTEnv i t2
  return t2
infer (Meta {ident = i} :< WeakTermThunk e) = do
  t <- infer e
  let result = WeakTypeDown t
  insTEnv i result
  return result
infer (Meta {ident = l} :< WeakTermUnthunk v) = do
  t <- infer v
  i <- newName
  insCEnv t (WeakTypeDown (WeakTypeHole i))
  let result = WeakTypeHole i
  insTEnv l result
  return result
infer (Meta {ident = i} :< WeakTermMu (s, t) e) = do
  insTEnv s t
  te <- infer e
  insCEnv (WeakTypeDown te) t
  insTEnv i te
  return te
infer (Meta {ident = i} :< WeakTermCase e ves) = do
  t <- infer e
  let (vs, es) = unzip ves
  tvs <- mapM inferPat vs
  forM_ tvs $ \tv -> insCEnv t tv
  ans <- WeakTypeHole <$> newName
  tes <- mapM infer es
  forM_ tes $ \te -> insCEnv ans te
  insTEnv i ans
  return ans
infer (Meta {ident = i} :< WeakTermAsc e t) = do
  te <- infer e
  insCEnv t te
  insTEnv i te
  return te

inferPat :: Pat -> WithEnv WeakType
inferPat (Meta {ident = i} :< PatVar s) = do
  mt <- lookupTEnv s
  case mt of
    Just t -> do
      insTEnv i t
      return t
    Nothing -> do
      new <- WeakTypeHole <$> newName
      insTEnv s new
      insTEnv i new
      return new
inferPat (Meta {ident = i} :< PatConst s) = do
  mt <- lookupVEnv s
  case mt of
    Just t -> do
      let t' = weakenValueType t
      insTEnv i t'
      return t'
    Nothing -> lift $ throwE $ "const " ++ s ++ " is not defined"
inferPat (Meta {ident = l} :< PatApp e v) = do
  te <- inferPat e
  tv <- inferPat v
  i <- newName
  insTEnv i (WeakTypeHole i)
  j <- newName
  insTEnv j tv
  insCEnv te (WeakTypeNode (j, tv) (WeakTypeHole i))
  let result = WeakTypeHole i
  insTEnv l result
  return result

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
unify ((WeakTypeForall (i, tdom1) tcod1, WeakTypeForall (j, tdom2) tcod2):cs)
  | i == j =
    unify $
    (WeakTypeHole i, WeakTypeHole j) : (tdom1, tdom2) : (tcod1, tcod2) : cs
unify ((WeakTypeUp t1, WeakTypeUp t2):cs) = unify $ (t1, t2) : cs
unify ((WeakTypeDown t1, WeakTypeDown t2):cs) = unify $ (t1, t2) : cs
unify ((WeakTypeUniv i, WeakTypeUniv j):cs) = do
  insLEnv i j
  unify cs
unify ((t1, t2):cs) =
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
sType sub (WeakTypeConst s) = WeakTypeConst s
sType sub (WeakTypeUp t) = do
  let t' = sType sub t
  WeakTypeUp t'
sType sub (WeakTypeDown t) = do
  let t' = sType sub t
  WeakTypeDown t'
sType _ (WeakTypeUniv i) = WeakTypeUniv i
sType sub (WeakTypeForall (s, tdom) tcod) = do
  let tdom' = sType sub tdom
  let tcod' = sType sub tcod
  WeakTypeForall (s, tdom') tcod'

sTypeName :: [(String, String)] -> WeakType -> WeakType
sTypeName _ (WeakTypeVar s) = WeakTypeVar s
sTypeName _ (WeakTypeHole s) = WeakTypeHole s
sTypeName sub (WeakTypeConst s) = WeakTypeConst s
sTypeName sub (WeakTypeUp t) = do
  let t' = sTypeName sub t
  WeakTypeUp t'
sTypeName sub (WeakTypeDown t) = do
  let t' = sTypeName sub t
  WeakTypeDown t'
sTypeName _ (WeakTypeUniv i) = WeakTypeUniv i
sTypeName sub (WeakTypeForall (s, tdom) tcod) = do
  let tdom' = sTypeName sub tdom
  let tcod' = sTypeName sub tcod
  WeakTypeForall (s, tdom') tcod'

sConstraint :: Subst -> Constraint -> Constraint
sConstraint s = map (\(t1, t2) -> (sType s t1, sType s t2))
