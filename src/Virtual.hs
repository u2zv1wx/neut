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
virtualV (Value (VMeta {vtype = vt} :< ValueVar s)) =
  return $ vt :< DataPointer s
virtualV (Value (VMeta {vtype = vt} :< ValueNodeApp s [])) =
  return $ vt :< DataCell s []
virtualV (Value (VMeta {vtype = vt} :< ValueNodeApp s vs)) = do
  vs' <- mapM (virtualV . Value) vs
  return $ vt :< DataCell s vs'
virtualV (Value (VMeta {vtype = vt} :< ValueThunk c i)) = do
  asm <- virtualC c
  unthunkIdents <- lookupThunkEnv i
  forM_ unthunkIdents $ \j -> do
    let newName = "thunk" ++ i ++ "unthunk" ++ j
    liftIO $ putStrLn $ "creating thunk with name: " ++ newName
    asm' <- liftIO $ newIORef asm
    insCodeEnv newName asm'
  return $ vt :< DataLabel i

virtualC :: Comp -> WithEnv Code
virtualC (Comp (CMeta {ctype = ct} :< CompLam _ e)) = do
  _ :< code <- virtualC (Comp e)
  return $ ct :< code
virtualC (Comp (CMeta {ctype = ct} :< CompApp e@(CMeta {ctype = ect} :< _) v)) = do
  case ect of
    CompTypeForall (i, _) _ -> do
      e' <- virtualC (Comp e)
      v' <- virtualV v
      return $ ct :< CodeLet i v' e'
    _ -> do
      lift $ throwE $ "virtualC.CompApp. Note:\n " ++ Pr.ppShow ct
virtualC (Comp (CMeta {ctype = ct} :< CompRet v)) = do
  asm <- virtualV v
  return $ ct :< CodeReturn asm
virtualC (Comp (CMeta {ctype = ct} :< CompBind s c1 c2)) = do
  operation1 <- virtualC (Comp c1)
  operation2 <- virtualC (Comp c2)
  traceLet ct s operation1 operation2
virtualC (Comp (CMeta {ctype = ct} :< CompUnthunk v@(Value (VMeta {vtype = ValueTypeDown tct} :< _)) j)) = do
  operand <- virtualV v
  let args = forallArgs tct
  case operand of
    _ :< DataPointer s   -> return $ ct :< CodeJump s j args -- indirect branch
    _ :< DataLabel label -> return $ ct :< CodeJump label j args -- direct branch
    _                    -> lift $ throwE "virtualC.CompUnthunk"
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
  return $ ct :< CodeJump s s (forallArgs ct)
virtualC (Comp (CMeta {ctype = ct} :< CompCase vs tree)) = do
  fooList <-
    forM vs $ \v -> do
      vt :< asm <- virtualV v
      i <- newName
      return ((i, vt), vt :< asm)
  let (is, asms) = unzip fooList
  body <- virtualDecision ct is tree
  let _ :< code = letSeq asms (map fst is) body
  return $ ct :< code

virtualDecision ::
     CompType -> [(Identifier, ValueType)] -> Decision PreComp -> WithEnv Code
virtualDecision ct asmList (DecisionLeaf ois preComp) = do
  let indexList = map fst ois
  let forEach = flip map
  let asmList' =
        forEach (zip asmList indexList) $ \((x, vt), (index, ot)) -> do
          ot :< DataElemAtIndex (vt :< DataPointer x) index
  let varList = map (fst . snd) ois
  body <- virtualC $ Comp preComp
  return $ letSeq asmList' varList body
virtualDecision ct ((x, vt):vs) (DecisionSwitch (o, ot) cs mdefault) = do
  jumpList <- virtualCase ct ((x, vt) : vs) cs
  defaultJump <- virtualDefaultCase ct ((x, vt) : vs) mdefault
  let selector = ot :< DataElemAtIndex (vt :< DataPointer x) o
  return $ makeBranch ct selector jumpList defaultJump
virtualDecision ct _ (DecisionSwap _ _) = undefined
virtualDecision _ [] t =
  lift $ throwE $ "virtualDecision. Note: \n" ++ Pr.ppShow t

virtualCase ::
     CompType
  -> [(Identifier, ValueType)]
  -> [(Identifier, Decision PreComp)]
  -> WithEnv JumpList
virtualCase _ _ [] = return []
virtualCase ct vs ((cons, tree):cs) = do
  code <- virtualDecision ct vs tree
  codeRef <- liftIO $ newIORef code
  label <- newName
  insCodeEnv label codeRef
  jumpList <- virtualCase ct vs cs
  return $ (cons, label) : jumpList

virtualDefaultCase ::
     CompType
  -> [(Identifier, ValueType)]
  -> Maybe (Maybe Identifier, Decision PreComp)
  -> WithEnv (Maybe (Maybe Identifier, Identifier))
virtualDefaultCase ct _ Nothing = return Nothing
virtualDefaultCase ct vs (Just (mx, tree)) = do
  code <- virtualDecision ct vs tree
  codeRef <- liftIO $ newIORef code
  label <- newName
  insCodeEnv label codeRef
  return $ Just (mx, label)

type JumpList = [(Identifier, Identifier)]

makeBranch ::
     CompType
  -> Data
  -> JumpList
  -> Maybe (Maybe Identifier, Identifier)
  -> Code
makeBranch _ _ [] Nothing = error "empty branch"
makeBranch ct d js@((_, target):_) Nothing = do
  ct :< CodeSwitch d target js
makeBranch ct d@(vt :< _) js (Just (Just x, label)) =
  ct :< CodeLet x d (ct :< CodeSwitch (vt :< DataPointer x) label js)
makeBranch ct d js (Just (Nothing, label)) = ct :< CodeSwitch d label js

letSeq :: [Data] -> [Identifier] -> Code -> Code
letSeq [] [] code = code
letSeq (d:ds) (i:is) code@(ct :< _) = ct :< CodeLet i d (letSeq ds is code)
letSeq _ _ _ = error "Virtual.letSeq: invalid arguments"

traceLet :: CompType -> String -> Code -> Code -> WithEnv Code
traceLet ct s (_ :< CodeReturn o) cont = return $ ct :< CodeLet s o cont
traceLet ct s (_ :< CodeJump addr j args) cont = do
  liftIO $ putStrLn $ "Found CodeJump with Let. The ident is " ++ show j ++ "."
  corresondingThunk <- lookupThunkEnv j
  case corresondingThunk of
    [i] -> do
      let newName = "thunk" ++ i ++ "unthunk" ++ j
      appendCode ct s cont newName
      return $ ct :< CodeJump addr newName args
    [] -> return $ ct :< CodeCall s addr args cont -- non-tail call
    _ ->
      lift $
      throwE $
      "multiple thunk found for an unthunk: \n" ++ show corresondingThunk
traceLet ct s (_ :< CodeLet k o1 o2) cont = do
  c <- traceLet ct s o2 cont
  return $ ct :< CodeLet k o1 c
traceLet ct s (_ :< CodeCall k i args o) cont = do
  c <- traceLet ct s o cont
  return $ ct :< CodeCall k i args c
traceLet ct s (_ :< switcher@(CodeSwitch _ defaultBranch branchList)) cont = do
  appendCode ct s cont defaultBranch
  forM_ branchList $ \(_, label) -> appendCode ct s cont label
  return $ ct :< switcher

appendCode :: CompType -> Identifier -> Code -> Identifier -> WithEnv ()
appendCode ct s cont key = do
  mcode <- lookupCodeEnv key
  case mcode of
    Nothing -> lift $ throwE $ "no such code: " ++ show key
    Just coderef -> do
      code <- liftIO $ readIORef coderef
      code' <- traceLet ct s code cont
      liftIO $ writeIORef coderef code'

forallArgs :: CompType -> [Identifier]
forallArgs (CompTypeForall (i, _) t) = i : forallArgs t
forallArgs _                         = []
