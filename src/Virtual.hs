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
virtualV (Value (i :< ValueVar s)) = return $ DataPointer s
virtualV (Value (i :< ValueConst s)) = return $ DataCell s []
virtualV (Value (i :< ValueNodeApp s vs)) = do
  vs' <- mapM (virtualV . Value) vs
  return $ DataCell s vs'
virtualV (Value (Meta {ident = i} :< ValueThunk c)) = do
  asm <- virtualC c
  corresondingUnthunkIdents <- lookupThunkEnv i
  forM_ corresondingUnthunkIdents $ \j -> do
    let newName = "thunk" ++ i ++ "unthunk" ++ j
    liftIO $ putStrLn $ "creating thunk with name: " ++ newName
    asm' <- liftIO $ newIORef asm
    insCodeEnv newName asm' -- the generated code can be looked up via the identifier of unthunk
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
  traceLet s operation1 operation2
virtualC (Comp (Meta {ident = i} :< CompUnthunk v)) = do
  operand <- virtualV v
  case operand of
    DataPointer s   -> return $ CodeJump s i -- indirect branch?
    DataLabel label -> return $ CodeJump label i -- this shouldn't occur (by optimization)
    _               -> lift $ throwE "virtualC.CUnthunk"
virtualC (Comp (i :< CompMu s c)) = undefined
virtualC (Comp (i :< CompCase c vcs)) = undefined

traceLet :: String -> Code -> Code -> WithEnv Code
traceLet s (CodeAllocate o) cont = return $ CodeLet s o cont
traceLet s (CodeJump addr j) cont = do
  liftIO $ putStrLn $ "Found CodeJump with Let. The ident is " ++ show j ++ "."
  corresondingThunk <- lookupThunkEnv j
  case corresondingThunk of
    [i] -> do
      let newName = "thunk" ++ i ++ "unthunk" ++ j
      mcode <- lookupCodeEnv newName
      case mcode of
        Nothing -> undefined -- recursive
        Just coderef -> do
          code <- liftIO $ readIORef coderef
          liftIO $ putStrLn $ "corresponding thunk is " ++ show i
          code' <- traceLet s code cont
          liftIO $ writeIORef coderef code'
          -- insCodeEnv i code'
          return $ CodeJump addr newName
    _ -> lift $ throwE "multiple or zero thunk found for an unthunk"
traceLet s (CodeLet k o1 o2) cont = do
  c <- traceLet s o2 cont
  return $ CodeLet k o1 c
