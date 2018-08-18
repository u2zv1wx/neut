module Lift where

import           Control.Comonad.Cofree
import           Control.Monad
import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Data

liftV :: QuasiValue -> WithEnv QuasiValue
liftV v@(QuasiValue (_ :< ValueVar _)) = return v
liftV v@(QuasiValue (_ :< ValueNodeApp _ [])) = return v
liftV (QuasiValue (i :< ValueNodeApp s vs)) = do
  vs' <- mapM (liftV . QuasiValue) vs
  vs'' <- forM vs' $ \(QuasiValue v) -> return v
  return $ QuasiValue $ i :< ValueNodeApp s vs''
liftV (QuasiValue (i :< ValueThunk c)) = do
  c' <- liftC c
  return $ QuasiValue $ i :< ValueThunk c'

liftC :: QuasiComp -> WithEnv QuasiComp
liftC (QuasiComp (i :< QuasiCompLam x e)) = do
  QuasiComp e' <- liftC $ QuasiComp e
  return $ QuasiComp $ i :< QuasiCompLam x e'
liftC (QuasiComp (i :< QuasiCompApp e v)) = do
  QuasiComp e' <- liftC $ QuasiComp e
  v' <- liftV v
  return $ QuasiComp $ i :< QuasiCompApp e' v'
liftC (QuasiComp (i :< QuasiCompRet v)) = do
  v' <- liftV v
  return $ QuasiComp $ i :< QuasiCompRet v'
liftC (QuasiComp (i :< QuasiCompBind s c1 c2)) = do
  QuasiComp c1' <- liftC (QuasiComp c1)
  QuasiComp c2' <- liftC (QuasiComp c2)
  return $ QuasiComp $ i :< QuasiCompBind s c1' c2'
liftC (QuasiComp (i :< QuasiCompUnthunk v)) = do
  v' <- liftV v
  return $ QuasiComp $ i :< QuasiCompUnthunk v'
liftC (QuasiComp (meta :< QuasiCompMu s c)) = do
  c' <- liftC (QuasiComp c)
  let freeVarsInBody = varN c'
  newArgs <-
    forM freeVarsInBody $ \(vmeta, _) -> do
      i <- newName
      return (vmeta, i)
  let f2b = zip (map snd freeVarsInBody) newArgs
  QuasiComp c'' <- supplyC s f2b c'
  -- mu x. M ~> (mu x. Lam (y1 ... yn). M) @ k1 @ ... @ kn
  let QuasiComp absC = compLamSeq (map snd newArgs) $ QuasiComp c''
  -- let ct' = forallSeq newArgs ct -- update the type of `mu x. M`
  let muAbsC = meta :< QuasiCompMu s absC
  appMuAbsC <- appFold (QuasiComp muAbsC) freeVarsInBody
  return $ appMuAbsC
  -- let QuasiComp absC = compLamSeq (map snd newArgs) $ QuasiComp c''
  -- return $ QuasiComp $ meta :< QuasiCompMu s absC
  -- let ct' = forallSeq newArgs ct -- update the type of `mu x. M`
  -- let muAbsC = CMeta {ctype = ct'} :< QuasiCompMu s absC
  -- insVTEnv s $ ValueTypeDown ct'
  -- appMuAbsC <- appFold (QuasiComp muAbsC) freeVarsInBody
  -- undefined
  -- return $ appMuAbsC
liftC (QuasiComp (i :< QuasiCompCase vs vcs)) = do
  vs' <- mapM liftV vs
  let (patList, bodyList) = unzip vcs
  bodyList' <- mapM (liftC . QuasiComp) bodyList
  let bodyList'' = map (\(QuasiComp c) -> c) bodyList'
  -- vcs' <- liftDecision vcs
  return $ QuasiComp $ i :< QuasiCompCase vs' (zip patList bodyList'')

-- liftDecision ::
--      Decision (Cofree (CompF Value) Meta)
--   -> WithEnv (Decision (Cofree (CompF Value) Meta))
-- liftDecision (DecisionLeaf xs c) = do
--   Comp c' <- liftC $ Comp c
--   return $ DecisionLeaf xs c'
-- liftDecision (DecisionSwitch o ids Nothing) = do
--   let (is, ds) = unzip ids
--   ds' <- mapM liftDecision ds
--   return $ DecisionSwitch o (zip is ds') Nothing
-- liftDecision (DecisionSwitch o ids (Just (i, tree))) = do
--   let (is, ds) = unzip ids
--   ds' <- mapM liftDecision ds
--   tree' <- liftDecision tree
--   return $ DecisionSwitch o (zip is ds') (Just (i, tree'))
-- liftDecision (DecisionSwap i d) = do
--   d' <- liftDecision d
--   return $ DecisionSwap i d'
type VIdentifier = (Meta, Identifier)

supplyV ::
     Identifier
  -> [(Identifier, VIdentifier)]
  -> QuasiValue
  -> WithEnv QuasiValue
-- supplyV self args (Value (meta :< ValueVar s))
--   | s == self = do
--     let ct' = forallSeq (map snd args) ct -- update the type of `x` in `mu x. M`
--     return $ Value $ meta :< ValueVar s
supplyV _ f2b v@(QuasiValue (_ :< ValueVar s)) = do
  case lookup s f2b of
    Nothing        -> return v
    Just (meta, b) -> return $ QuasiValue $ meta :< ValueVar b -- replace free vars
supplyV _ _ v@(QuasiValue (_ :< ValueNodeApp _ [])) = return v
supplyV self args (QuasiValue (i :< ValueNodeApp s vs)) = do
  vs' <- mapM (supplyV self args . QuasiValue) vs
  let vs'' = map (\(QuasiValue v) -> v) vs'
  return $ QuasiValue $ i :< ValueNodeApp s vs''
supplyV self args (QuasiValue (i :< ValueThunk c)) = do
  c' <- supplyC self args c
  return $ QuasiValue $ i :< ValueThunk c'

supplyC ::
     Identifier -> [(Identifier, VIdentifier)] -> QuasiComp -> WithEnv QuasiComp
supplyC self args (QuasiComp (i :< QuasiCompLam x e)) = do
  QuasiComp e' <- supplyC self args (QuasiComp e)
  return $ QuasiComp $ i :< QuasiCompLam x e'
supplyC self args (QuasiComp (i :< QuasiCompApp e v)) = do
  QuasiComp e' <- supplyC self args (QuasiComp e)
  v' <- supplyV self args v
  return $ QuasiComp $ i :< QuasiCompApp e' v'
supplyC self args (QuasiComp (i :< QuasiCompRet v)) = do
  v' <- supplyV self args v
  return $ QuasiComp $ i :< QuasiCompRet v'
supplyC self args (QuasiComp (i :< QuasiCompBind s c1 c2)) = do
  QuasiComp c1' <- supplyC self args (QuasiComp c1)
  QuasiComp c2' <- supplyC self args (QuasiComp c2)
  return $ QuasiComp $ i :< QuasiCompBind s c1' c2'
supplyC self args (QuasiComp inner@(i :< QuasiCompUnthunk v)) = do
  v' <- supplyV self args v
  liftIO $
    putStrLn $ "found unthunk. self == " ++ show self ++ ", v == " ++ show v'
  case v' of
    QuasiValue (_ :< ValueVar s)
      | s == self -> do
        liftIO $ putStrLn "updating"
        let args' = map snd args
        c' <- appFold (QuasiComp inner) args'
        return c'
    _ -> return $ QuasiComp $ i :< QuasiCompUnthunk v'
supplyC self args (QuasiComp (i :< QuasiCompMu s c)) = do
  QuasiComp c' <- supplyC self args $ QuasiComp c
  return $ QuasiComp $ i :< QuasiCompMu s c'
supplyC self args (QuasiComp (i :< QuasiCompCase vs vcs)) = do
  vs' <- mapM (supplyV self args) vs
  let (patList, bodyList) = unzip vcs
  bodyList' <- mapM (supplyC self args . QuasiComp) bodyList
  let bodyList'' = map (\(QuasiComp c) -> c) bodyList'
  -- vcs' <- supplyDecision self args vcs
  return $ QuasiComp $ i :< QuasiCompCase vs' (zip patList bodyList'')
  -- undefined
  -- return $ QuasiComp $ i :< QuasiCompCase vs' vcs'

varP :: QuasiValue -> [(Meta, Identifier)]
varP (QuasiValue (meta :< ValueVar s))     = [(meta, s)]
varP (QuasiValue (_ :< ValueNodeApp _ vs)) = join $ map (varP . QuasiValue) vs
varP (QuasiValue (_ :< ValueThunk e))      = varN e

varN :: QuasiComp -> [(Meta, Identifier)]
varN (QuasiComp (_ :< QuasiCompLam s e)) =
  filter (\(_, t) -> t /= s) $ varN (QuasiComp e)
varN (QuasiComp (_ :< QuasiCompApp e v)) = varN (QuasiComp e) ++ varP v
varN (QuasiComp (_ :< QuasiCompRet v)) = varP v
varN (QuasiComp (_ :< QuasiCompBind s e1 e2)) =
  varN (QuasiComp e1) ++ filter (\(_, t) -> t /= s) (varN (QuasiComp e2))
varN (QuasiComp (_ :< QuasiCompUnthunk v)) = varP v
varN (QuasiComp (_ :< QuasiCompMu s e)) =
  filter (\(_, t) -> t /= s) (varN (QuasiComp e))
varN (QuasiComp (_ :< QuasiCompCase vs vses)) = do
  let efs = join $ map varP vs
  let (patList, bodyList) = unzip vses
  let vs1 = join $ join $ map (map varPat) patList
  let vs2 = join $ map (varN . QuasiComp) bodyList
  -- let vars = varDecision tree
  efs ++ vs1 ++ vs2

varPat :: Pat -> [(Meta, Identifier)]
varPat (_ :< PatHole)     = []
varPat (meta :< PatVar s) = [(meta, s)]
varPat (_ :< PatApp _ ps) = join $ map varPat ps

compLamSeq :: [Identifier] -> QuasiComp -> QuasiComp
compLamSeq [] terminal = terminal
compLamSeq (x:xs) c@(QuasiComp (meta :< _)) = do
  let QuasiComp tmp = compLamSeq xs c
  QuasiComp $ meta :< QuasiCompLam x tmp

appFold :: QuasiComp -> [VIdentifier] -> WithEnv QuasiComp
appFold e [] = return e
appFold (QuasiComp e) ((meta, i):ts) = do
  let arg = meta :< ValueVar i
  -- let tmp = CompApp e (Value $ Meta {vtype = vt} :< ValueVar i)
  k <- newName
  let tmp = Meta {ident = k} :< QuasiCompApp e (QuasiValue arg)
  appFold (QuasiComp tmp) ts
  -- appFold (Comp $ Meta {ctype = cod} :< tmp) ts
  -- case ct of
  --   CompTypeForall _ cod -> do
  --     let tmp = CompApp e (Value $ Meta {vtype = vt} :< ValueVar i)
  --     appFold (Comp $ Meta {ctype = cod} :< tmp) ts
  --   _ -> do
  --     lift $ throwE $ "Lift.appFold. Note: \n" ++ show ct
