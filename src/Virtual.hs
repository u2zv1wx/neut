module Virtual where

import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data
import           Data.IORef

import           Control.Comonad.Cofree

import qualified Text.Show.Pretty           as Pr

virtualV :: Value -> WithEnv Data
virtualV (Value (_ :< ValueVar s)) = return $ DataPointer s
virtualV (Value (_ :< ValueConst s)) = return $ DataCell s []
virtualV (Value (_ :< ValueNodeApp s vs)) = do
  vs' <- mapM (virtualV . Value) vs
  return $ DataCell s vs'
virtualV (Value (VMeta {vtype = vt} :< ValueThunk c)) = do
  case vt of
    ValueTypeDown _ i -> do
      asm <- virtualC c
      unthunkIdents <- lookupThunkEnv i
      forM_ unthunkIdents $ \j -> do
        let newName = "thunk" ++ i ++ "unthunk" ++ j
        liftIO $ putStrLn $ "creating thunk with name: " ++ newName
        asm' <- liftIO $ newIORef asm
        insCodeEnv newName asm'
      return $ DataLabel i
    _ -> lift $ throwE $ "virtualV.ValueThunk"

virtualC :: Comp -> WithEnv Code
virtualC (Comp (_ :< CompLam _ e)) = virtualC (Comp e)
virtualC (Comp (_ :< CompApp e@(CMeta {ctype = ct} :< _) v)) = do
  case ct of
    CompTypeForall (i, _) _ -> do
      e' <- virtualC (Comp e)
      v' <- virtualV v
      return $ CodeLet i v' e'
    _ -> do
      lift $ throwE $ "virtualC.CompApp. Note:\n " ++ Pr.ppShow ct
virtualC (Comp (_ :< CompRet v)) = do
  asm <- virtualV v
  return $ CodeAllocate asm
virtualC (Comp (_ :< CompBind s c1 c2)) = do
  operation1 <- virtualC (Comp c1)
  operation2 <- virtualC (Comp c2)
  traceLet s operation1 operation2
virtualC (Comp (_ :< CompUnthunk v@(Value (VMeta {vtype = vt} :< _)))) = do
  case vt of
    ValueTypeDown ct i -> do
      operand <- virtualV v
      let args = forallArgs ct
      case operand of
        DataPointer s   -> return $ CodeJump s i args
        DataLabel label -> return $ CodeJump label i args
        _               -> lift $ throwE "virtualC.CompUnthunk"
    _ -> lift $ throwE "virtualC.CompUnthunk"
virtualC (Comp (CMeta {ctype = ct} :< CompMu s c)) = do
  asm <- virtualC $ Comp c
  asm' <- liftIO $ newIORef asm
  insCodeEnv s asm'
  return $ CodeJump s s (forallArgs ct)
virtualC (Comp (_ :< CompCase _ _)) = undefined

traceLet :: String -> Code -> Code -> WithEnv Code
traceLet s (CodeAllocate o) cont = return $ CodeLet s o cont
traceLet s (CodeJump addr j args) cont = do
  liftIO $ putStrLn $ "Found CodeJump with Let. The ident is " ++ show j ++ "."
  corresondingThunk <- lookupThunkEnv j
  case corresondingThunk of
    [i] -> do
      let newName = "thunk" ++ i ++ "unthunk" ++ j
      mcode <- lookupCodeEnv newName
      case mcode of
        Nothing -> return $ CodeCall s addr args cont -- non-tail call
        Just coderef -> do
          code <- liftIO $ readIORef coderef
          liftIO $ putStrLn $ "corresponding thunk is " ++ show i
          code' <- traceLet s code cont
          liftIO $ writeIORef coderef code'
          return $ CodeJump addr newName args
    _ -> lift $ throwE "multiple or zero thunk found for an unthunk"
traceLet s (CodeLet k o1 o2) cont = do
  c <- traceLet s o2 cont
  return $ CodeLet k o1 c
traceLet s (CodeCall k i args o) cont = do
  c <- traceLet s o cont
  return $ CodeCall k i args c

forallArgs :: CompType -> [Identifier]
forallArgs (CompTypeForall (i, _) t) = i : forallArgs t
forallArgs _                         = []
