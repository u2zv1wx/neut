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
  e' <- prepare e
  _ <- infer e'
  env <- get
  let cs = constraintEnv env
  liftIO $ putStrLn $ "CONSTRAINTS===="
  liftIO $ putStrLn $ Pr.ppShow cs
  liftIO $ putStrLn $ "CONSTRAINTS===="
  sub <- Typing.unify cs
  env <- get
  let regionInequalities = regionConstraintEnv env
  -- liftIO $ putStrLn $ "SUB===="
  -- liftIO $ putStrLn $ Pr.ppShow cs
  -- liftIO $ putStrLn $ "SUB===="
  liftIO $ putStrLn $ "INEQUALITIES===="
  liftIO $ putStrLn $ Pr.ppShow regionInequalities
  liftIO $ putStrLn $ "INEQUALITIES===="
  -- let nameTree = constructMap nameEquations
  -- liftIO $ putStrLn $ "MARK===="
  -- liftIO $ putStrLn $ Pr.ppShow nameTree
  -- liftIO $ putStrLn $ "MARK===="
  -- let tenv' = map (\(s, t) -> (s, sType nameTree t)) $ rTypeEnv env
  -- modify (\e -> e {rTypeEnv = tenv'})
  return ()

prepare :: MTerm -> WithEnv MTerm
prepare (Var s, meta) = do
  r <- lookupRNEnv' s
  return (Var s, meta {regionSet = [r]})
prepare (Const s, meta) = do
  r <- lookupRNEnv' s
  return (Const s, meta {regionSet = [r]})
prepare (Lam (S s p) e, meta) = do
  r <- newRegion
  insRNEnv s r
  e' <- prepare e
  return (Lam (S s p) e', meta)
prepare (App e v, meta) = do
  e' <- prepare e
  v' <- prepare v
  return (App e' v', meta)
prepare (ConsApp v1 v2, meta) = do
  v1' <- prepare v1
  v2' <- prepare v2
  r <- newRegion
  return (ConsApp v1' v2', meta {regionSet = [r]})
prepare (Ret v, meta) = do
  v' <- prepare v
  return (Ret v', meta)
prepare (Bind (S s p) e1 e2, meta) = do
  e1' <- prepare e1
  r <- newRegion
  insRNEnv s r
  e2' <- prepare e2
  return (Bind (S s p) e1' e2', meta)
prepare (Thunk e, meta) = do
  e' <- prepare e
  r <- newRegion
  return (Thunk e', meta {regionSet = [r]})
prepare (Unthunk v, meta) = do
  v' <- prepare v
  return (Unthunk v', meta)
prepare (Send s e, meta) = do
  e' <- prepare e
  return (Send s e', meta)
prepare (Recv (S s p) e, meta) = do
  r <- newRegion
  insRNEnv s r
  e' <- prepare e
  return (Recv (S s p) e, meta)
prepare (Dispatch e1 e2, meta) = do
  e1' <- prepare e1
  e2' <- prepare e2
  return (Dispatch e1' e2', meta)
prepare (Coleft e, meta) = do
  e' <- prepare e
  return (Coleft e', meta)
prepare (Coright e, meta) = do
  e' <- prepare e
  return (Coright e', meta)
prepare (Mu s e, meta) = do
  e' <- prepare e
  return (Mu s e', meta)
prepare (Case v ves, meta) = do
  v' <- prepare v
  let (vs, es) = unzip ves
  vs' <- mapM preparePat vs
  es' <- mapM prepare es
  return (Case v' (zip vs' es'), meta)
prepare (Asc e t, meta) = do
  e' <- prepare e
  return (Asc e' t, meta)

preparePat :: MTerm -> WithEnv MTerm
preparePat (Var s, meta) = do
  r <- newRegion
  insRNEnv s r
  return (Var s, meta {regionSet = [r]})
preparePat (Const s, meta) = do
  r <- lookupRNEnv' s
  return (Const s, meta {regionSet = [r]})
preparePat (ConsApp v1 v2, meta) = do
  v1' <- prepare v1
  v2' <- prepare v2
  r <- newRegion
  return (ConsApp v1' v2', meta {regionSet = [r]})
preparePat _ = lift $ throwE "Region.preparePat"

infer :: MTerm -> WithEnv Type
infer (Var s, Meta {ident = i}) = lookupTEnv' s >>= regAndRet i
infer (Const s, Meta {ident = i, regionSet = [r]}) =
  lookupTEnv' s >>= annotate r >>= regAndRet i
infer (Lam (S s _) e, Meta {ident = i}) = do
  r <- lookupRNEnv' s
  tdom <- lookupTEnv' s >>= annotate r
  insTEnv s tdom
  tcod <- infer e
  regAndRet i $ TForall (S s tdom) tcod
infer (App e v, Meta {ident = i}) = do
  te <- infer e
  tv <- infer v
  case (te, tv) of
    (TForall (S _ tdom) tcod, targ) -> do
      insCEnv tdom targ -- the actual arguments ("v") must live longer than formal ones ("x").
      regAndRet i tcod
    _ -> lift $ throwE $ "Region.infer.App. Note:\n" ++ Pr.ppShow (e, te, tv)
infer (ConsApp v1 v2, Meta {ident = i}) = do
  t1 <- infer v1
  t2 <- infer v2
  liftIO $ putStrLn $ Pr.ppShow t2
  case (t1, t2) of
    (RType (TNode (S _ tdom) tcod) _, targ) -> do
      insCEnv tdom targ -- the actual arguments ("v") must live longer than formal ones ("x").
      regAndRet i tcod
    _ -> lift $ throwE $ "Region.infer.ConsApp. Note:\n" ++ Pr.ppShow (t1, t2)
infer (Ret v, Meta {ident = i}) = do
  tv <- infer v
  regAndRet i $ TUp tv
infer (Bind (S s _) e1 e2, Meta {ident = i}) = do
  t1 <- infer e1
  r <- lookupRNEnv' s
  ts <- lookupTEnv' s >>= annotate r
  insTEnv s ts
  t2 <- infer e2
  case t1 of
    TUp p
      -- the actual arguments ("e : ↑P") must live longer than formal ones ("x : P").
      -- for example, consider an expression `let x := zero in foo`. the `x` in the expression
      -- is expected to live shorter that `zero`.
     -> do
      insCEnv p ts
      regAndRet i t2
    _ -> lift $ throwE "Region.infer.Bind"
infer (Thunk e, Meta {ident = i, regionSet = [r]}) = do
  t <- infer e
  forM_ (freeVar e) $ \v -> do
    rt <- lookupTEnv v
    case rt of
      Just (RType _ r') -> insRCEnv r r' -- the freevars in a thunk must live longer than the thunk
      _ ->
        lift $ throwE $ "Region.infer.Region. Note:\n" ++ Pr.ppShow (v, rt, e)
  regAndRet i $ RType (TDown t) r
infer (Unthunk v, Meta {ident = i}) = do
  tv <- infer v
  case tv of
    RType (TDown n) _ -> instantiate n >>= regAndRet i
    _ -> lift $ throwE $ "Region.infer.Unthunk. Note:\n" ++ Pr.ppShow (v, tv)
infer (Send (S s t) e, Meta {ident = i}) = infer e >>= regAndRet i
infer (Recv (S s t) e, Meta {ident = i}) = do
  r <- lookupRNEnv' s
  ts <- lookupTEnv' s >>= annotate r
  insTEnv s ts
  infer e >>= regAndRet i
infer (Dispatch e1 e2, Meta {ident = i}) = do
  t1 <- infer e1
  t2 <- infer e2
  regAndRet i $ TCotensor t1 t2
infer (Coleft e, Meta {ident = i}) = do
  t <- infer e
  case t of
    TCotensor t1 _ -> regAndRet i t1
    _              -> lift $ throwE "Region.infer.Coleft"
infer (Coright e, Meta {ident = i}) = do
  t <- infer e
  case t of
    TCotensor _ t2 -> regAndRet i t2
    _              -> lift $ throwE "Region.infer.Coright"
infer (Mu (S s _) e, Meta {ident = i}) = do
  r <- lookupRNEnv' s
  targ <- lookupTEnv' s >>= annotate r
  insTEnv s targ
  tbody <- infer e
  -- a == b iff a <= b && b <= a
  insCEnv (TDown tbody) targ
  insCEnv targ (TDown tbody)
  regAndRet i tbody
infer (Case v ves, Meta {ident = i}) = do
  tv <- infer v
  let (vs, es) = unzip ves
  tvs <- mapM inferPat vs
  tes <- mapM infer es
  forM_ (map (\s -> (s, tv)) tvs) $ uncurry insCEnv -- lifetime(vars in pattern) <= lifetime(v)
  y <- THole <$> newName
  -- all the lifetimes of the bodies are equal
  forM_ (map (\s -> (s, y)) tes) $ uncurry insCEnv
  forM_ (map (\s -> (y, s)) tes) $ uncurry insCEnv
  regAndRet i (head tes)
infer (Asc e t, Meta {ident = i}) = infer e

inferPat :: MTerm -> WithEnv Type
inferPat (Var s, Meta {ident = i, regionSet = [r]}) =
  lookupTEnv' s >>= annotate r >>= regAndRet i
inferPat (Const s, Meta {ident = i, regionSet = [r]}) =
  lookupTEnv' s >>= annotate r >>= regAndRet i
inferPat (ConsApp v1 v2, Meta {ident = i}) = do
  t1 <- infer v1
  t2 <- infer v2
  case (t1, t2) of
    (RType (TNode (S _ tdom) tcod) _, targ) -> do
      insCEnv tdom targ
      regAndRet i tcod
    _ ->
      lift $ throwE $ "Region.inferPat.ConsApp. Note:\n" ++ Pr.ppShow (t1, t2)
inferPat _ = lift $ throwE "Region.inferPat"

newRegion :: WithEnv String
newRegion = newNameWith "region"

regAndRet :: String -> Type -> WithEnv Type
-- regAndRet i (RType t r) = insRTEnv i (RType t r) >> return t
regAndRet i t = insRTEnv i t >> return t

lookupTEnv' :: String -> WithEnv Type
lookupTEnv' s = do
  t <- lookupTEnv s
  case t of
    Just t  -> return t
    Nothing -> lift $ throwE $ "Region.lookupTEnv' : not found : " ++ show s

lookupRNEnv' :: String -> WithEnv String
lookupRNEnv' s = do
  t <- lookupRNEnv s
  case t of
    Just t  -> return t
    Nothing -> lift $ throwE $ "Region.lookupRNEnv' : not found : " ++ show s

instantiate :: Type -> WithEnv Type
instantiate (TForall (S s (RType dom r)) cod) = do
  r' <- newRegion
  cod' <- instantiate cod
  return $ TForall (S s (RType dom r')) cod'
instantiate t = return t

annotate :: String -> Type -> WithEnv Type
annotate r t = do
  t' <- annotate' t
  case t' of
    (RType t'' _) -> return (RType t'' r)
    _ -> lift $ throwE $ "Region.annotate. Note:\n" ++ Pr.ppShow t'

annotate' :: Type -> WithEnv Type
annotate' (TVar s) = RType (TConst s) <$> newRegion
annotate' (THole s) = lift $ throwE "Region.annotate'.THole"
annotate' (TConst s) = RType (TConst s) <$> newRegion
annotate' (TNode (S s p1) p2) = do
  p1' <- annotate' p1
  p2' <- annotate' p2
  RType (TNode (S s p1') p2') <$> newRegion
annotate' (TUp p) = TUp <$> annotate' p
annotate' (TDown n) = do
  n' <- annotate' n
  RType (TDown n') <$> newRegion
annotate' (TUniv l) = RType (TUniv l) <$> newRegion
annotate' (TForall (S s p) n) = do
  p' <- annotate' p
  n' <- annotate' n
  return $ TForall (S s p') n'
annotate' (TCotensor n1 n2) = do
  n1' <- annotate' n1
  n2' <- annotate' n2
  return $ TCotensor n1' n2'
annotate' (RType p r) = lift $ throwE "Region.annotate'.RType"

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

sTerm :: (Region, Region) -> MTerm -> MTerm
sTerm sub (Var s, i) = (Var s, sMeta sub i)
sTerm sub (Const s, i) = (Const s, sMeta sub i)
sTerm sub (ConsApp v1 v2, i) = do
  let v1' = sTerm sub v1
  let v2' = sTerm sub v2
  (ConsApp v1' v2', sMeta sub i)
sTerm sub (Thunk e, i) = do
  let e' = sTerm sub e
  (Thunk e', sMeta sub i)
sTerm sub (Lam (S s t) e, i) = do
  let e' = sTerm sub e
  (Lam (S s t) e', sMeta sub i)
sTerm sub (App e v, i) = do
  let e' = sTerm sub e
  let v' = sTerm sub v
  (App e' v', sMeta sub i)
sTerm sub (Ret v, i) = do
  let v' = sTerm sub v
  (Ret v', sMeta sub i)
sTerm sub (Bind (S s t) e1 e2, i) = do
  let e1' = sTerm sub e1
  let e2' = sTerm sub e2
  (Bind (S s t) e1' e2', sMeta sub i)
sTerm sub (Unthunk v, i) = do
  let v' = sTerm sub v
  (Unthunk v', sMeta sub i)
sTerm sub (Send (S s t) e, i) = do
  let e' = sTerm sub e
  (Send (S s t) e', sMeta sub i)
sTerm sub (Recv (S s t) e, i) = do
  let e' = sTerm sub e
  (Recv (S s t) e', sMeta sub i)
sTerm sub (Dispatch e1 e2, i) = do
  let e1' = sTerm sub e1
  let e2' = sTerm sub e2
  (Dispatch e1' e2', sMeta sub i)
sTerm sub (Coleft e, i) = do
  let e' = sTerm sub e
  (Coleft e', sMeta sub i)
sTerm sub (Coright e, i) = do
  let e' = sTerm sub e
  (Coright e', sMeta sub i)
sTerm sub (Mu (S s t) e, i) = do
  let e' = sTerm sub e
  (Mu (S s t) e', sMeta sub i)
sTerm sub (Case e ves, i) = do
  let e' = sTerm sub e
  let (vs, es) = unzip ves
  let vs' = map (sTerm sub) vs
  let es' = map (sTerm sub) es
  (Case e' (zip vs' es'), sMeta sub i)
sTerm sub (Asc e t, _) = sTerm sub e

sMeta :: (Region, Region) -> Meta -> Meta
sMeta (from, to) meta =
  if regionSet meta == [from]
    then meta {regionSet = [to]}
    else meta

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

data RegTree
  = RegAtom Meta
  | RegNode Meta
            [RegTree]
  deriving (Show, Eq)

toRegTree :: MTerm -> RegTree
toRegTree (Var s, i) = RegAtom i
toRegTree (Const _, i) = RegAtom i
toRegTree (ConsApp v1 v2, i) = RegNode i [toRegTree v1, toRegTree v2]
toRegTree (Thunk e, i) = RegNode i [toRegTree e]
toRegTree (Lam (S s t) e, i) = RegNode i [toRegTree e]
toRegTree (App e v, i) = RegNode i [toRegTree e, toRegTree v]
toRegTree (Ret v, i) = RegNode i [toRegTree v]
toRegTree (Bind (S s t) e1 e2, i) = RegNode i [toRegTree e1, toRegTree e2]
toRegTree (Unthunk v, i) = RegNode i [toRegTree v]
toRegTree (Send (S s t) e, i) = RegNode i [toRegTree e]
toRegTree (Recv (S s t) e, i) = RegNode i [toRegTree e]
toRegTree (Dispatch e1 e2, i) = RegNode i [toRegTree e1, toRegTree e2]
toRegTree (Coleft e, i) = RegNode i [toRegTree e]
toRegTree (Coright e, i) = RegNode i [toRegTree e]
toRegTree (Mu (S s t) e, i) = RegNode i [toRegTree e]
toRegTree (Case e ves, i) = do
  let (vs, es) = unzip ves
  let vs' = map toRegTree vs
  let es' = map toRegTree es
  RegNode i $ toRegTree e : vs' ++ es'
toRegTree (Asc e t, _) = toRegTree e

-- region集合をchildからinheritするように書き換える
setify :: MTerm -> MTerm
setify = undefined

qux :: [(Region, Region)] -> MTerm -> MTerm
qux = undefined

-- inequalityに沿ってregionSetをenrichする
foo :: (Region, Region) -> MTerm -> MTerm
foo = undefined

-- a <= bにそって書き換えたいとして、このaが先に見つかった状況を扱う。
-- childにbが現れたならばsubstを行う。
-- childでsubstが行われていたならば (つまりsubstがemptyでなければ) 自分もsubstする。
bar :: Region -> MTerm -> (MTerm, Subst)
bar = undefined
