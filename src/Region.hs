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
  return ()

type Region = String

infer :: MTerm -> WithEnv Type
infer (Var s, _) = lookupTEnv' s
infer (Const s, _) = lookupTEnv' s >>= annotate
infer (Lam (S s _) e, _) = do
  tdom <- lookupTEnv' s >>= annotate
  insTEnv s tdom
  tcod <- infer e
  return $ TForall (S s tdom) tcod
infer (App e v, _) = do
  te <- infer e
  tv <- infer v
  case (te, tv) of
    (TForall (S _ tdom) tcod, targ) -> do
      insCEnv tdom targ
      return tcod
    _ -> lift $ throwE $ "Region.infer.App. Note:\n" ++ Pr.ppShow (e, te, tv)
infer (ConsApp v1 v2, _) = do
  t1 <- infer v1
  t2 <- infer v2
  case (t1, t2) of
    (RType (TNode (S _ tdom) tcod) _, targ) -> do
      insCEnv tdom targ
      return tcod
    _ -> lift $ throwE $ "Region.infer.ConsApp. Note:\n" ++ Pr.ppShow (t1, t2)
infer (Ret v, i) = do
  tv <- infer v
  return $ TUp tv
infer (Bind (S s _) e1 e2, i) = do
  t1 <- infer e1
  ts <- lookupTEnv' s >>= annotate
  insTEnv s ts
  t2 <- infer e2
  case t1 of
    TUp p -> do
      insCEnv p ts
      return t2
    _ -> lift $ throwE "Region.infer.Bind"
infer (Thunk e, _) = do
  t <- infer e
  RType (TDown t) <$> newRegion
infer (Unthunk v, _) = do
  tv <- infer v
  case tv of
    RType (TDown n) _ -> instantiate n
    _ -> lift $ throwE $ "Region.infer.Unthunk. Note:\n" ++ Pr.ppShow (v, tv)

-- infer (Send (S s t) e, _) = undefined
-- infer (Recv (S s t) e, _) = undefined
-- infer (Dispatch e1 e2, _) = do
--   t1 <- infer e1
--   t2 <- infer e2
--   return $ TCotensor t1 t2
-- infer (Coleft e, _) = do
--   t <- infer e
--   case t of
--     TCotensor t1 _ -> return t1
--     _              -> lift $ throwE "Region.infer.Coleft"
-- infer (Coright e, _) = do
--   t <- infer e
--   case t of
--     TCotensor _ t2 -> return t2
--     _              -> lift $ throwE "Region.infer.Coright"
-- infer (Mu (S s t) e, _) = do
--   r <- newRegion
--   insRNEnv s r
--   infer e
-- infer (Case v ves, _) = do
--   tv <- infer v
--   case tv of
--     RType t r -> do
--       let (vs, es) = unzip ves
--       mapM_ (inferPat r) vs
--       es' <- mapM infer es
--       case es' of
--         (tbody:_) -> return tbody
--         _         -> lift $ throwE "Region.infer.Case"
--     _ -> lift $ throwE "Region.infer.Case"
-- infer (Asc e t, i) = infer e
-- type Region = String
-- inferPat :: Region -> MTerm -> WithEnv Type
-- inferPat r (Var s, i) = do
--   t <- lookupTEnv' i
--   insRNEnv s r
--   return $ RType t r
-- inferPat _ (Const s, i) = do
--   t <- lookupTEnv' i
--   mr <- lookupRNEnv s
--   case mr of
--     Nothing -> lift $ throwE "Region.inferPat.Const"
--     Just r  -> return $ RType t r
-- inferPat r (ConsApp v1 v2, _) = do
--   t1 <- inferPat r v1
--   t2 <- inferPat r v2
--   case (t1, t2) of
--     (TNode (S s (RType tdom r1)) tcod, RType tv r2) -> do
--       insRCEnv r1 r2
--       return tcod
--     _ -> lift $ throwE "Region.inferPat.ConsApp"
-- inferPat _ _ = lift $ throwE "Region.inferPat"
newRegion :: WithEnv String
newRegion = newNameWith "region"

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

traceMap :: String -> [(Child, Parent)] -> String
traceMap child xs =
  case lookup child xs of
    Nothing     -> child
    Just parent -> traceMap parent xs
