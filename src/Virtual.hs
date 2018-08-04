module Virtual where

import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data

import           Control.Comonad.Cofree

import qualified Text.Show.Pretty           as Pr

virtualV :: Value -> WithEnv Data
virtualV (Value (i :< ValueVar s)) = return $ DataPointer s
virtualV (Value (i :< ValueConst s)) = return $ DataCell s []
virtualV (Value (i :< ValueNodeApp s vs)) = do
  vs' <- mapM (virtualV . Value) vs
  return $ DataCell s vs'
virtualV (Value (i :< ValueThunk c)) = do
  asm <- virtualC c
  i <- newNameWith "code"
  insCodeEnv i asm
  return $ DataLabel i

virtualC :: Comp -> WithEnv Code
virtualC (Comp (i :< CompLam _ e)) = virtualC (Comp e)
virtualC (Comp (_ :< CompApp e@(Meta {ident = i} :< _) v)) = do
  mt <- lookupTEnv i
  liftIO $ putStrLn "==========↓↓↓↓ CompApp ↓↓↓↓==========="
  liftIO $ putStrLn $ Pr.ppShow mt
  liftIO $ putStrLn "==========↑↑↑↑ CompApp ↑↑↑↑==========="
  case mt of
    Just (TypeCompType (CompTypeForall (i, _) _)) -> do
      e' <- virtualC (Comp e)
      v' <- virtualV v
      return $ CodeLet i v' e'
    _ -> lift $ throwE $ "virtualC.CompApp. Note:\n " ++ Pr.ppShow mt
virtualC (Comp (i :< CompRet v)) = do
  asm <- virtualV v
  return $ CodeAllocate asm
virtualC (Comp (i :< CompBind s c1 c2)) = do
  operation1 <- virtualC (Comp c1)
  operation2 <- virtualC (Comp c2)
  return $ traceLet s operation1 operation2
virtualC (Comp (i :< CompUnthunk v)) = do
  operand <- virtualV v
  case operand of
    DataPointer s   -> return $ CodeJump s -- indirect branch?
    DataLabel label -> return $ CodeJump label -- this shouldn't occur (by optimization)
    _               -> lift $ throwE "virtualC.CUnthunk"
virtualC (Comp (i :< CompMu s c)) = undefined
virtualC (Comp (i :< CompCase c vcs)) = undefined

traceLet :: String -> Code -> Code -> Code
traceLet s (CodeAllocate o) cont  = CodeLet s o cont
traceLet s (CodeJump addr) cont   = CodeCall s addr cont
traceLet s (CodeLet k o1 o2) cont = CodeLet k o1 (traceLet s o2 cont)
