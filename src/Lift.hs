module Lift where

import           Control.Comonad.Cofree
import           Control.Monad
import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Data

liftV :: Value -> WithEnv Value
liftV v@(Value (_ :< ValueVar _)) = return v
liftV v@(Value (_ :< ValueNodeApp s [])) = return v
liftV (Value (i :< ValueNodeApp s vs)) = do
  vs' <- mapM (liftV . Value) vs
  vs'' <- forM vs' $ \(Value v) -> return v
  return $ Value $ i :< ValueNodeApp s vs''
liftV (Value (i :< ValueThunk c j)) = do
  c' <- liftC c
  return $ Value $ i :< ValueThunk c' j

liftC :: Comp -> WithEnv Comp
liftC (Comp (i :< CompLam x e)) = do
  Comp e' <- liftC $ Comp e
  return $ Comp $ i :< CompLam x e'
liftC (Comp (i :< CompApp e v)) = do
  Comp e' <- liftC $ Comp e
  v' <- liftV v
  return $ Comp $ i :< CompApp e' v'
liftC (Comp (i :< CompRet v)) = do
  v' <- liftV v
  return $ Comp $ i :< CompRet v'
liftC (Comp (i :< CompBind s c1 c2)) = do
  Comp c1' <- liftC (Comp c1)
  Comp c2' <- liftC (Comp c2)
  return $ Comp $ i :< CompBind s c1' c2'
liftC (Comp (i :< CompUnthunk v j)) = do
  v' <- liftV v
  return $ Comp $ i :< CompUnthunk v' j
liftC (Comp (CMeta {ctype = ct} :< CompMu s c)) = do
  c' <- liftC (Comp c)
  let freeVarsInBody = varN c'
  newArgs <-
    forM freeVarsInBody $ \(vt, _) -> do
      i <- newName
      return (vt, i)
  let f2b = zip (map snd freeVarsInBody) newArgs
  Comp c'' <- supplyC s f2b c'
  -- mu x. M ~> (mu x. Lam (y1 ... yn). M) @ k1 @ ... @ kn
  let Comp absC = compLamSeq newArgs $ Comp c''
  let ct' = forallSeq newArgs ct -- update the type of `mu x. M`
  let muAbsC = CMeta {ctype = ct'} :< CompMu s absC
  appMuAbsC <- appFold (Comp muAbsC) freeVarsInBody
  return $ appMuAbsC
liftC (Comp (i :< CompCase v vcs)) = do
  v' <- liftV v
  vcs' <-
    forM vcs $ \(pat, c) -> do
      Comp c' <- liftC (Comp c)
      return (pat, c')
  return $ Comp $ i :< CompCase v' vcs'

type VIdentifier = (VMeta, Identifier)

supplyV :: Identifier -> [(Identifier, VIdentifier)] -> Value -> WithEnv Value
supplyV self args (Value (VMeta {vtype = ValueTypeDown ct} :< ValueVar s))
  | s == self = do
    let ct' = forallSeq (map snd args) ct -- update the type of `x` in `mu x. M`
    return $ Value $ VMeta {vtype = ValueTypeDown ct'} :< ValueVar s
supplyV _ f2b v@(Value (_ :< ValueVar s)) = do
  case lookup s f2b of
    Nothing         -> return v
    Just (vmeta, b) -> return $ Value $ vmeta :< ValueVar b -- replace free vars
supplyV _ _ v@(Value (_ :< ValueNodeApp s [])) = return v
supplyV self args (Value (i :< ValueNodeApp s vs)) = do
  vs' <- mapM (supplyV self args . Value) vs
  let vs'' = map (\(Value v) -> v) vs'
  return $ Value $ i :< ValueNodeApp s vs''
supplyV self args (Value (i :< ValueThunk c j)) = do
  c' <- supplyC self args c
  return $ Value $ i :< ValueThunk c' j

supplyC :: Identifier -> [(Identifier, VIdentifier)] -> Comp -> WithEnv Comp
supplyC self args (Comp (i :< CompLam x e)) = do
  Comp e' <- supplyC self args (Comp e)
  return $ Comp $ i :< CompLam x e'
supplyC self args (Comp (i :< CompApp e v)) = do
  Comp e' <- supplyC self args (Comp e)
  v' <- supplyV self args v
  return $ Comp $ i :< CompApp e' v'
supplyC self args (Comp (i :< CompRet v)) = do
  v' <- supplyV self args v
  return $ Comp $ i :< CompRet v'
supplyC self args (Comp (i :< CompBind s c1 c2)) = do
  Comp c1' <- supplyC self args (Comp c1)
  Comp c2' <- supplyC self args (Comp c2)
  return $ Comp $ i :< CompBind s c1' c2'
supplyC self args (Comp inner@(i :< CompUnthunk v j)) = do
  v' <- supplyV self args v
  case v' of
    Value (_ :< ValueVar s)
      | s == self -> do
        let args' = map snd args
        c' <- appFold (Comp inner) args'
        return c'
    _ -> return $ Comp $ i :< CompUnthunk v' j
supplyC self args (Comp (i :< CompMu s c)) = do
  Comp c' <- supplyC self args $ Comp c
  return $ Comp $ i :< CompMu s c'
supplyC self args (Comp (i :< CompCase v vcs)) = do
  v' <- supplyV self args v
  vcs' <-
    forM vcs $ \(v, c) -> do
      Comp c' <- supplyC self args $ Comp c
      return (v, c')
  return $ Comp $ i :< CompCase v' vcs'

varP :: Value -> [(VMeta, Identifier)]
varP (Value (meta :< ValueVar s))     = [(meta, s)]
varP (Value (_ :< ValueNodeApp _ vs)) = join $ map (varP . Value) vs
varP (Value (_ :< ValueThunk e _))    = varN e

varN :: Comp -> [(VMeta, Identifier)]
varN (Comp (_ :< CompLam s e)) = filter (\(_, t) -> t /= s) $ varN (Comp e)
varN (Comp (_ :< CompApp e v)) = varN (Comp e) ++ varP v
varN (Comp (_ :< CompRet v)) = varP v
varN (Comp (_ :< CompBind s e1 e2)) =
  varN (Comp e1) ++ filter (\(_, t) -> t /= s) (varN (Comp e2))
varN (Comp (_ :< CompUnthunk v _)) = varP v
varN (Comp (_ :< CompMu s e)) = filter (\(_, t) -> t /= s) (varN (Comp e))
varN (Comp (_ :< CompCase e ves)) = do
  let efs = varP e
  vefss <-
    forM ves $ \(pat, body) -> do
      let bound = varPat pat
      let fs = varN $ Comp body
      return $ filter (\(_, k) -> k `notElem` bound) fs
  efs ++ join vefss

varPat :: Pat -> [Identifier]
varPat (_ :< PatVar s)    = [s]
varPat (_ :< PatApp _ ps) = join $ map varPat ps

compLamSeq :: [(VMeta, Identifier)] -> Comp -> Comp
compLamSeq [] terminal = terminal
compLamSeq ((VMeta {vtype = vt}, x):xs) c@(Comp (CMeta {ctype = ct} :< _)) = do
  let Comp tmp = compLamSeq xs c
  Comp $ CMeta {ctype = CompTypeForall (x, vt) ct} :< CompLam x tmp

forallSeq :: [(VMeta, Identifier)] -> CompType -> CompType
forallSeq [] t = t
forallSeq ((VMeta {vtype = vt}, i):ts) t = do
  let tmp = forallSeq ts t
  CompTypeForall (i, vt) tmp

appFold :: Comp -> [(VMeta, Identifier)] -> WithEnv Comp
appFold e [] = return e
appFold (Comp e@(CMeta {ctype = ct} :< _)) ((VMeta {vtype = vt}, i):ts) = do
  case ct of
    CompTypeForall _ cod -> do
      let tmp = CompApp e (Value $ VMeta {vtype = vt} :< ValueVar i)
      appFold (Comp $ CMeta {ctype = cod} :< tmp) ts
    _ -> do
      lift $ throwE $ "Lift.appFold. Note: \n" ++ show ct
