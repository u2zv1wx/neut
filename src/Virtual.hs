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

import           Debug.Trace

virtualV :: Value -> WithEnv Data
virtualV (Value (_ :< ValueVar s)) = return $ DataPointer s
virtualV (Value (_ :< ValueNodeApp s [])) = return $ DataCell s []
virtualV (Value (_ :< ValueNodeApp s vs)) = do
  vs' <- mapM (virtualV . Value) vs
  return $ DataCell s vs'
virtualV (Value (_ :< ValueThunk c i)) = do
  asm <- virtualC c
  unthunkIdents <- lookupThunkEnv i
  forM_ unthunkIdents $ \j -> do
    let newName = "thunk" ++ i ++ "unthunk" ++ j
    liftIO $ putStrLn $ "creating thunk with name: " ++ newName
    asm' <- liftIO $ newIORef asm
    insCodeEnv newName asm'
  return $ DataLabel i

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
  return $ CodeReturn asm
virtualC (Comp (_ :< CompBind s c1 c2)) = do
  operation1 <- virtualC (Comp c1)
  operation2 <- virtualC (Comp c2)
  traceLet s operation1 operation2
virtualC (Comp (_ :< CompUnthunk v@(Value (VMeta {vtype = ValueTypeDown ct} :< _)) j)) = do
  operand <- virtualV v
  let args = forallArgs ct
  case operand of
    DataPointer s   -> return $ CodeJump s j args -- indirect branch
    DataLabel label -> return $ CodeJump label j args -- direct branch
    _               -> lift $ throwE "virtualC.CompUnthunk"
virtualC (Comp (_ :< CompUnthunk (Value (VMeta {vtype = _} :< _)) _)) = do
  lift $ throwE "virtualC.CompUnthunk"
virtualC (Comp (CMeta {ctype = ct} :< CompMu s c)) = do
  current <- getFunName
  setFunName s
  insEmptyFunEnv s
  asm <- virtualC $ Comp c
  asm' <- liftIO $ newIORef asm
  insCodeEnv s asm'
  setFunName current
  return $ CodeJump s s (forallArgs ct)
virtualC (Comp (_ :< CompCase vs tree)) = do
  fooList <-
    forM vs $ \v -> do
      asm <- virtualV v
      i <- newName
      return (i, asm)
  let (is, asms) = unzip fooList
  body <- virtualDecision is tree
  return $ letSeq asms is body

virtualDecision :: [Identifier] -> Decision PreComp -> WithEnv Code
virtualDecision asmList (DecisionLeaf ois preComp) = do
  let indexList = map fst ois
  let forEach = flip map
  let asmList' =
        forEach (zip asmList indexList) $ \(asm, index) -> do
          DataElemAtIndex (DataPointer asm) index
  let varList = map snd ois
  body <- virtualC $ Comp preComp
  return $ letSeq asmList' varList body
virtualDecision (x:vs) (DecisionSwitch o cs mdefault) = do
  jumpList <- virtualCase (x : vs) cs
  defaultJump <- virtualDefaultCase (x : vs) mdefault
  let selector = DataElemAtIndex (DataPointer x) o
  return $ makeBranch selector jumpList defaultJump
virtualDecision _ (DecisionSwap _ _) = undefined
virtualDecision [] t =
  lift $ throwE $ "virtualDecision. Note: \n" ++ Pr.ppShow t

virtualCase ::
     [Identifier] -> [(Identifier, Decision PreComp)] -> WithEnv JumpList
virtualCase _ [] = return []
virtualCase vs ((cons, tree):cs) = do
  code <- virtualDecision vs tree
  codeRef <- liftIO $ newIORef code
  label <- newName
  insCodeEnv label codeRef
  jumpList <- virtualCase vs cs
  return $ (cons, label) : jumpList

virtualDefaultCase ::
     [Identifier]
  -> Maybe (Maybe Identifier, Decision PreComp)
  -> WithEnv (Maybe (Maybe Identifier, Identifier))
virtualDefaultCase _ Nothing = return Nothing
virtualDefaultCase vs (Just (mx, tree)) = do
  code <- virtualDecision vs tree
  codeRef <- liftIO $ newIORef code
  label <- newName
  insCodeEnv label codeRef
  return $ Just (mx, label)

type JumpList = [(Identifier, Identifier)]

makeBranch :: Data -> JumpList -> Maybe (Maybe Identifier, Identifier) -> Code
makeBranch _ [] Nothing = error "empty branch"
makeBranch d js@((_, target):_) Nothing = do
  CodeSwitch d target js
makeBranch d js (Just (Just x, label)) =
  CodeLet x d (CodeSwitch (DataPointer x) label js)
makeBranch d js (Just (Nothing, label)) = CodeSwitch d label js

letSeq :: [Data] -> [Identifier] -> Code -> Code
letSeq [] [] code         = code
letSeq (d:ds) (i:is) code = CodeLet i d (letSeq ds is code)
letSeq _ _ _              = error "Virtual.letSeq: invalid arguments"

traceLet :: String -> Code -> Code -> WithEnv Code
traceLet s (CodeReturn o) cont = return $ CodeLet s o cont
traceLet s (CodeJump addr j args) cont = do
  liftIO $ putStrLn $ "Found CodeJump with Let. The ident is " ++ show j ++ "."
  corresondingThunk <- lookupThunkEnv j
  case corresondingThunk of
    [i] -> do
      let newName = "thunk" ++ i ++ "unthunk" ++ j
      mcode <- lookupCodeEnv newName
      case mcode of
        Nothing -> lift $ throwE $ "Virutal.traceLet"
        Just coderef -> do
          code <- liftIO $ readIORef coderef
          liftIO $ putStrLn $ "corresponding thunk is " ++ show i
          code' <- traceLet s code cont
          liftIO $ writeIORef coderef code'
          return $ CodeJump addr newName args
    [] -> return $ CodeCall s addr args cont -- non-tail call
    _ ->
      lift $
      throwE $
      "multiple thunk found for an unthunk: \n" ++ show corresondingThunk
traceLet s (CodeLet k o1 o2) cont = do
  c <- traceLet s o2 cont
  return $ CodeLet k o1 c
traceLet s (CodeCall k i args o) cont = do
  c <- traceLet s o cont
  return $ CodeCall k i args c

forallArgs :: CompType -> [Identifier]
forallArgs (CompTypeForall (i, _) t) = i : forallArgs t
forallArgs _                         = []
