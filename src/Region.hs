module Region
  ( check
  , newRegion
  ) where

import           Control.Monad
import           Control.Monad.State
import           Control.Monad.Trans.Except

import qualified Text.Show.Pretty           as Pr

import           Data
import qualified Typing

-- eからregion名の制約を生成して、そっからregion名を同値関係で割って、
-- で、region名をその同値関係の代表元で統一する。
check :: MTerm -> WithEnv ()
check e = do
  modify (\e -> e {constraintEnv = []})
  _ <- infer e
  env <- get
  let cs = constraintEnv env
  liftIO $ putStrLn $ "CONSTRAINTS===="
  liftIO $ putStrLn $ Pr.ppShow cs
  liftIO $ putStrLn $ "CONSTRAINTS===="
  sub <- Typing.unify cs
  env <- get
  let nameEquations = regionConstraintEnv env
  -- liftIO $ putStrLn $ "SUB===="
  -- liftIO $ putStrLn $ Pr.ppShow cs
  -- liftIO $ putStrLn $ "SUB===="
  let nameTree = constructMap nameEquations
  liftIO $ putStrLn $ "MARK===="
  liftIO $ putStrLn $ Pr.ppShow nameTree
  liftIO $ putStrLn $ "MARK===="
  let tenv' = map (\(s, t) -> (s, sType nameTree t)) $ rTypeEnv env
  modify (\e -> e {rTypeEnv = tenv'})
  return ()

type Region = String

infer :: MTerm -> WithEnv Type
infer (Var s, i) = lookupTEnv' s >>= regAndRet i
infer (Const s, i) = lookupTEnv' s >>= annotate >>= regAndRet i
infer (Lam (S s _) e, i) = do
  tdom <- lookupTEnv' s >>= annotate
  insTEnv s tdom
  tcod <- infer e
  regAndRet i $ TForall (S s tdom) tcod
infer (App e v, i) = do
  te <- infer e
  tv <- infer v
  case (te, tv) of
    (TForall (S _ tdom) tcod, targ) -> do
      insCEnv tdom targ
      regAndRet i tcod
    _ -> lift $ throwE $ "Region.infer.App. Note:\n" ++ Pr.ppShow (e, te, tv)
infer (ConsApp v1 v2, i) = do
  t1 <- infer v1
  t2 <- infer v2
  case (t1, t2) of
    (RType (TNode (S _ tdom) tcod) _, targ) -> do
      insCEnv tdom targ
      regAndRet i tcod
    _ -> lift $ throwE $ "Region.infer.ConsApp. Note:\n" ++ Pr.ppShow (t1, t2)
infer (Ret v, i) = do
  tv <- infer v
  regAndRet i $ TUp tv
infer (Bind (S s _) e1 e2, i) = do
  t1 <- infer e1
  ts <- lookupTEnv' s >>= annotate
  insTEnv s ts
  t2 <- infer e2
  case t1 of
    TUp p -> do
      insCEnv p ts
      regAndRet i t2
    _ -> lift $ throwE "Region.infer.Bind"
infer (Thunk e, i) = do
  t <- infer e
  r <- newRegion
  forM_ (freeVar e) $ \v -> do
    rt <- lookupTEnv v
    case rt of
      Just (RType _ r') -> insRNEnv r r'
      _ ->
        lift $ throwE $ "Region.infer.Region. Note:\n" ++ Pr.ppShow (v, rt, e)
  regAndRet i $ RType (TDown t) r
infer (Unthunk v, i) = do
  tv <- infer v
  case tv of
    RType (TDown n) _ -> instantiate n >>= regAndRet i
    _ -> lift $ throwE $ "Region.infer.Unthunk. Note:\n" ++ Pr.ppShow (v, tv)
infer (Send (S s t) e, i) = infer e >>= regAndRet i
infer (Recv (S s t) e, i) = do
  ts <- lookupTEnv' s >>= annotate
  insTEnv s ts
  infer e >>= regAndRet i
infer (Dispatch e1 e2, i) = do
  t1 <- infer e1
  t2 <- infer e2
  regAndRet i $ TCotensor t1 t2
infer (Coleft e, i) = do
  t <- infer e
  case t of
    TCotensor t1 _ -> regAndRet i t1
    _              -> lift $ throwE "Region.infer.Coleft"
infer (Coright e, i) = do
  t <- infer e
  case t of
    TCotensor _ t2 -> regAndRet i t2
    _              -> lift $ throwE "Region.infer.Coright"
infer (Mu (S s t) e, i) = do
  ts <- lookupTEnv' s >>= annotate
  insTEnv s ts
  t <- infer e
  insCEnv (TDown t) ts
  regAndRet i t
infer (Case v ves, i) = do
  tv <- infer v
  let (vs, es) = unzip ves
  tvs <- mapM inferPat vs
  tes <- mapM infer es
  x <- THole <$> newName
  forM_ (map (\s -> (s, x)) (tv : tvs)) $ uncurry insCEnv
  y <- THole <$> newName
  forM_ (map (\s -> (s, y)) tes) $ uncurry insCEnv
  regAndRet i (head tes)
infer (Asc e t, i) = infer e

inferPat :: MTerm -> WithEnv Type
inferPat (Var s, i) = lookupTEnv' s >>= annotate >>= regAndRet i
inferPat (Const s, i) = lookupTEnv' s >>= annotate >>= regAndRet i
inferPat (ConsApp v1 v2, i) = do
  t1 <- infer v1
  t2 <- infer v2
  case (t1, t2) of
    (RType (TNode (S _ tdom) tcod) _, targ) -> do
      insCEnv tdom targ
      regAndRet i tcod
    _ -> lift $ throwE $ "Region.infer.ConsApp. Note:\n" ++ Pr.ppShow (t1, t2)
inferPat _ = lift $ throwE "Region.inferPat"

newRegion :: WithEnv String
newRegion = newNameWith "region"

regAndRet :: String -> Type -> WithEnv Type
regAndRet i t = insRTEnv i t >> return t

lookupTEnv' :: String -> WithEnv Type
lookupTEnv' s = do
  t <- lookupTEnv s
  case t of
    Just t  -> return t
    Nothing -> lift $ throwE $ "Region.lookupTEnv' : not found : " ++ show s

instantiate :: Type -> WithEnv Type
instantiate (TForall (S s (RType dom r)) cod) = do
  r' <- newRegion
  cod' <- instantiate cod
  return $ TForall (S s (RType dom r')) cod'
instantiate t = return t

annotate :: Type -> WithEnv Type
annotate (TVar s) = RType (TConst s) <$> newRegion
annotate (THole s) = lift $ throwE "Region.annotate.THole"
annotate (TConst s) = RType (TConst s) <$> newRegion
annotate (TNode (S s p1) p2) = do
  p1' <- annotate p1
  p2' <- annotate p2
  RType (TNode (S s p1') p2') <$> newRegion
annotate (TUp p) = TUp <$> annotate p
annotate (TDown n) = do
  n' <- annotate n
  RType (TDown n') <$> newRegion
annotate (TUniv l) = RType (TUniv l) <$> newRegion
annotate (TForall (S s p) n) = do
  p' <- annotate p
  n' <- annotate n
  return $ TForall (S s p') n'
annotate (TCotensor n1 n2) = do
  n1' <- annotate n1
  n2' <- annotate n2
  return $ TCotensor n1' n2'
annotate (RType p r) = lift $ throwE "Region.annotate.RType"

type Child = String

type Parent = String

type NameEquation = (String, String)

constructMap :: [NameEquation] -> [(Child, Parent)]
constructMap [] = []
constructMap ((a, b):es) = do
  let xs = constructMap es
  if a < b
    then (b, a) : xs
    else (a, b) : xs

type Root = String

type Subst = [(Child, Parent)]

traceMap :: [(Child, Parent)] -> Child -> Root
traceMap xs child =
  case lookup child xs of
    Nothing     -> child
    Just parent -> traceMap xs parent

sType :: Subst -> Type -> Type
sType _ (TVar s) = TVar s
sType _ (THole s) = THole s
sType _ (TConst s) = TConst s
sType sub (TNode (S s tdom) tcod) = do
  let tdom' = sType sub tdom
  let tcod' = sType sub tcod
  TNode (S s tdom') tcod'
sType sub (TNode (SHole s tdom) tcod) = do
  let tdom' = sType sub tdom
  let tcod' = sType sub tcod
  TNode (SHole s tdom') tcod'
sType sub (TUp t) = do
  let t' = sType sub t
  TUp t'
sType sub (TDown t) = do
  let t' = sType sub t
  TDown t'
sType _ (TUniv i) = TUniv i
sType sub (TForall (S s tdom) tcod) = do
  let tdom' = sType sub tdom
  let tcod' = sType sub tcod
  TForall (S s tdom') tcod'
sType sub (TForall (SHole s tdom) tcod) = do
  let tdom' = sType sub tdom
  let tcod' = sType sub tcod
  TForall (SHole s tdom') tcod'
sType sub (TCotensor t1 t2) = do
  let t1' = sType sub t1
  let t2' = sType sub t2
  TCotensor t1' t2'
sType sub (RType t r) = do
  let t' = sType sub t
  RType t' $ traceMap sub r

freeVar :: MTerm -> [String]
freeVar (Var s, _) = [s]
freeVar (Const _, _) = []
freeVar (ConsApp v1 v2, _) = freeVar v1 ++ freeVar v2
freeVar (Thunk e, _) = freeVar e
freeVar (Lam (S s t) e, _) = filter (/= s) $ freeVar e
freeVar (App e v, _) = freeVar e ++ freeVar v
freeVar (Ret v, _) = freeVar v
freeVar (Bind (S s t) e1 e2, _) = freeVar e1 ++ filter (/= s) (freeVar e2)
freeVar (Unthunk v, _) = freeVar v
freeVar (Send (S s t) e, _) = s : freeVar e
freeVar (Recv (S s t) e, _) = filter (/= s) (freeVar e)
freeVar (Dispatch e1 e2, _) = freeVar e1 ++ freeVar e2
freeVar (Coleft e, _) = freeVar e
freeVar (Coright e, _) = freeVar e
freeVar (Mu (S s t) e, _) = filter (/= s) (freeVar e)
freeVar (Case e ves, _) = do
  let efs = freeVar e
  vefss <-
    forM ves $ \(pat, body) -> do
      bound <- freeVar pat
      fs <- freeVar body
      return $ filter (`notElem` bound) fs
  efs ++ vefss
freeVar (Asc e t, _) = freeVar e
