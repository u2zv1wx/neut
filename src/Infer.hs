module Infer
  ( check
  , unify
  , checkType
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
  insTypeEnv main $ Fix $ TypeDown t -- insert the type of main function
  env <- get
  sub <- unify $ constraintEnv env
  let tenv' = map (\(s, t) -> (s, sType sub t)) $ typeEnv env
  modify (\e -> e {typeEnv = tenv', constraintEnv = []})

checkType :: Type -> WithEnv ()
checkType t = do
  _ <- inferType t
  env <- get
  sub <- unify $ constraintEnv env
  let tenv' = map (\(s, t) -> (s, sType sub t)) $ typeEnv env
  modify (\e -> e {typeEnv = tenv', constraintEnv = []})

infer :: Term -> WithEnv Type
infer (meta :< TermVar s) = do
  mt <- lookupTypeEnv s
  case mt of
    Just t -> do
      insTypeEnv meta t
      return t
    _ -> lift $ throwE $ "undefined variable: " ++ s
infer (meta :< TermConst s) = do
  t <- lookupTypeEnv' s
  insTypeEnv meta t
  return t
infer (meta :< TermThunk e) = do
  t <- infer e
  let result = Fix $ TypeDown t
  insTypeEnv meta result
  return result
infer (meta :< TermLam s e) = do
  j <- newName
  let tdom = Fix $ TypeHole j
  insTypeEnv s tdom
  te <- infer e
  let result = Fix $ TypeForall (s, tdom) te
  insTypeEnv meta result
  return result
infer (meta :< TermApp e v) = do
  te <- infer e
  tv <- infer v
  i <- newName
  let result = Fix $ TypeHole i
  j <- newName
  insTypeEnv j tv
  insConstraintEnv te (Fix $ TypeForall (j, tv) result)
  insTypeEnv meta result
  return result
infer (meta :< TermLift v) = do
  tv <- infer v
  insTypeEnv meta $ Fix $ TypeUp tv
  return $ Fix $ TypeUp tv
infer (meta :< TermBind x e1 e2) = do
  t1 <- infer e1
  i <- newName
  insConstraintEnv t1 (Fix $ TypeUp $ Fix $ TypeHole i)
  insTypeEnv x (Fix $ TypeHole i)
  result <- infer e2
  insTypeEnv meta result
  return result
infer (meta :< TermUnthunk v) = do
  t <- infer v
  i <- newName
  let result = Fix $ TypeHole i
  insConstraintEnv t (Fix $ TypeDown result)
  insTypeEnv meta result
  return result
infer (meta :< TermMu s e) = do
  j <- newName
  let trec = Fix $ TypeHole j
  insTypeEnv s trec
  te <- infer e
  insConstraintEnv (Fix $ TypeDown te) trec
  insTypeEnv meta te
  return te
infer (meta :< TermCase vs vses) = do
  tps <- mapM infer vs
  let (vss, es) = unzip vses
  tvss <- mapM (mapM inferPat) vss
  forM_ tvss $ \tvs -> forM_ (zip tps tvs) $ uncurry insConstraintEnv
  ans <- TypeHole <$> newName
  tes <- mapM infer es
  forM_ tes $ \te -> insConstraintEnv (Fix ans) te
  insTypeEnv meta (Fix ans)
  return $ Fix ans

inferType :: Type -> WithEnv Type
inferType (Fix TypeUnit) = do
  i <- newNameWith "level"
  return $ Fix (TypeUniv (WeakLevelHole i))
inferType (Fix (TypeInt _)) = do
  i <- newNameWith "level"
  return $ Fix (TypeUniv (WeakLevelHole i))
inferType (Fix TypeOpaque) = do
  i <- newNameWith "level"
  return $ Fix (TypeUniv (WeakLevelHole i))
inferType (Fix (TypeVar _)) = do
  i <- newNameWith "level"
  return $ Fix (TypeUniv (WeakLevelHole i))
inferType (Fix (TypeHole _)) = do
  i <- newNameWith "level"
  return $ Fix (TypeUniv (WeakLevelHole i))
inferType (Fix (TypeUp t)) = do
  u <- inferType t
  i <- newNameWith "level"
  return $ Fix (TypeUniv (WeakLevelHole i))
inferType (Fix (TypeDown t)) = do
  u <- inferType t
  i <- newNameWith "level"
  return $ Fix (TypeUniv (WeakLevelHole i))
inferType (Fix (TypeUniv _)) = do
  i <- newNameWith "level"
  -- TODO: add constraint: level < i
  return $ Fix (TypeUniv (WeakLevelHole i))
inferType (Fix (TypeForall (s, tdom) tcod)) = do
  insTypeEnv s tdom
  udom <- inferType tdom
  ucod <- inferType tcod
  i <- newNameWith "level"
  -- TODO: constraint: udom == ucod
  return $ Fix (TypeUniv (WeakLevelHole i))
inferType (Fix (TypeNode s ts)) = do
  us <- mapM inferType ts
  -- todo: constraint regarding us
  i <- newNameWith "level"
  return $ Fix (TypeUniv (WeakLevelHole i))
inferType (Fix (TypeStruct ts)) = do
  us <- mapM inferType ts
  i <- newNameWith "level"
  return $ Fix (TypeUniv (WeakLevelHole i))

inferPat :: Pat -> WithEnv Type
inferPat (meta :< PatHole) = do
  t <- TypeHole <$> newName
  insTypeEnv meta $ Fix t
  return $ Fix t
inferPat (meta :< PatConst x) = do
  t <- lookupTypeEnv' x
  insTypeEnv meta t
  return t
inferPat (meta :< PatVar s) = do
  mt <- lookupTypeEnv s
  case mt of
    Just t -> do
      insTypeEnv meta t
      return t
    _ -> do
      i <- newName
      insTypeEnv s $ Fix $ TypeHole i
      insTypeEnv meta (Fix (TypeHole i))
      return $ Fix (TypeHole i)
inferPat (meta :< PatApp v vs) = do
  t <- inferPat v
  let (cod, args) = forallArgs t
  ts <- mapM inferPat vs
  forM_ (zip ts (map snd args)) $ uncurry insConstraintEnv
  insTypeEnv meta cod
  return cod
inferPat (meta :< PatThunk v) = do
  t <- inferPat v
  insTypeEnv meta $ Fix $ TypeDown t
  return $ Fix $ TypeDown t
inferPat (meta :< PatUnthunk e) = do
  t <- inferPat e
  i <- newName
  let result = Fix $ TypeHole i
  insConstraintEnv t (Fix $ TypeDown result)
  insTypeEnv meta result
  return result

type Subst = [(String, Type)]

type Constraint = [(Type, Type)]

unify :: Constraint -> WithEnv Subst
unify [] = return []
unify ((Fix (TypeHole s), t2):cs) = do
  sub <- unify (sConstraint [(s, t2)] cs)
  return $ compose sub [(s, t2)]
unify ((t1, Fix (TypeHole s)):cs) = do
  sub <- unify (sConstraint [(s, t1)] cs)
  return $ compose sub [(s, t1)]
unify ((Fix (TypeVar s1), Fix (TypeVar s2)):cs)
  | s1 == s2 = unify cs
unify ((Fix (TypeForall (_, tdom1) tcod1), Fix (TypeForall (_, tdom2) tcod2)):cs) =
  unify $ (tdom1, tdom2) : (tcod1, tcod2) : cs
unify ((Fix (TypeNode x ts1), Fix (TypeNode y ts2)):cs)
  | x == y = unify $ zip ts1 ts2 ++ cs
unify ((Fix (TypeUp t1), Fix (TypeUp t2)):cs) = unify $ (t1, t2) : cs
unify ((Fix (TypeDown t1), Fix (TypeDown t2)):cs) = unify $ (t1, t2) : cs
unify ((Fix (TypeUniv i), Fix (TypeUniv j)):cs) = do
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
sType _ (Fix TypeUnit) = Fix TypeUnit
sType _ (Fix TypeOpaque) = Fix TypeOpaque
sType _ (Fix (TypeInt i)) = Fix $ TypeInt i
sType _ (Fix (TypeVar s)) = Fix $ TypeVar s
sType sub (Fix (TypeHole s)) =
  case lookup s sub of
    Nothing -> Fix $ TypeHole s
    Just t  -> t
sType sub (Fix (TypeUp t)) = do
  let t' = sType sub t
  Fix $ TypeUp t'
sType sub (Fix (TypeDown t)) = do
  let t' = sType sub t
  Fix $ TypeDown t'
sType _ (Fix (TypeUniv i)) = Fix $ TypeUniv i
sType sub (Fix (TypeForall (s, tdom) tcod)) = do
  let tdom' = sType sub tdom
  let tcod' = sType sub tcod
  Fix $ TypeForall (s, tdom') tcod'
sType sub (Fix (TypeNode s ts)) = do
  let ts' = map (sType sub) ts
  Fix $ TypeNode s ts'
sType sub (Fix (TypeStruct ts)) = do
  let ts' = map (sType sub) ts
  Fix $ TypeStruct ts'

sConstraint :: Subst -> Constraint -> Constraint
sConstraint s = map (\(t1, t2) -> (sType s t1, sType s t2))
