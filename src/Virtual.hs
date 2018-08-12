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

import           Data.Functor.Foldable

virtualV :: Value -> WithEnv UData
virtualV (Value (_ :< ValueVar s)) = do
  return $ Fix (DataPointer s)
virtualV (Value (_ :< ValueNodeApp s vs)) = do
  vs' <- mapM (virtualV . Value) vs
  return $ Fix $ DataCell s vs'
virtualV (Value (_ :< ValueThunk c i)) = do
  asm <- virtualC c
  unthunkIdents <- lookupThunkEnv i
  forM_ unthunkIdents $ \j -> do
    let newName = "thunk" ++ i ++ "unthunk" ++ j
    liftIO $ putStrLn $ "creating thunk with name: " ++ newName
    asm' <- liftIO $ newIORef asm
    insCodeEnv newName asm'
  return $ Fix $ DataLabel i

virtualC :: Comp -> WithEnv UCode
virtualC (Comp (_ :< CompLam _ e)) = do
  virtualC (Comp e)
virtualC (Comp (_ :< CompApp e@(CMeta {ctype = ect} :< _) v)) = do
  case ect of
    CompTypeForall (i, _) _ -> do
      v' <- virtualV v
      e' <- virtualC (Comp e)
      return $ Fix $ CodeLet i v' e'
    _ -> do
      lift $ throwE $ "virtualC.CompApp. Note:\n " ++ Pr.ppShow ect
virtualC (Comp (_ :< CompRet v)) = do
  asm <- virtualV v
  return $ Fix $ CodeReturn asm
virtualC (Comp (_ :< CompBind s c1 c2)) = do
  operation1 <- virtualC (Comp c1)
  operation2 <- virtualC (Comp c2)
  traceLet s operation1 operation2
virtualC (Comp (_ :< CompUnthunk v@(Value (VMeta {vtype = ValueTypeDown tct} :< _)) j)) = do
  operand <- virtualV v
  let args = forallArgs tct
  case operand of
    Fix (DataPointer s)   -> return $ Fix $ CodeJump s j args -- indirect branch
    Fix (DataLabel label) -> return $ Fix $ CodeJump label j args -- direct branch
    _                     -> lift $ throwE "virtualC.CompUnthunk"
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
  return $ Fix $ CodeJump s s (forallArgs ct)
virtualC (Comp (_ :< CompCase vs tree)) = do
  fooList <-
    forM vs $ \v -> do
      asm <- virtualV v
      i <- newName
      return (i, asm)
  let (is, asms) = unzip fooList
  body <- virtualDecision is tree
  let code = letSeq asms is body
  return $ code

virtualDecision :: [Identifier] -> Decision PreComp -> WithEnv UCode
virtualDecision asmList (DecisionLeaf ois preComp) = do
  let indexList = map fst ois
  let forEach = flip map
  let varList = map (fst . snd) ois
  asmList' <-
    forM (zip asmList ois) $ \(x, ((index, _), _)) -> do
      return $ Fix $ DataElemAtIndex (Fix $ DataPointer x) index
  body <- virtualC $ Comp preComp
  return $ letSeq asmList' varList body
virtualDecision (x:vs) (DecisionSwitch (o, _) cs mdefault)
  -- let vt' = traceLowType o vt
 = do
  let selector = Fix $ DataElemAtIndex (Fix $ DataPointer x) o
  jumpList <- virtualCase (x : vs) cs
  defaultJump <- virtualDefaultCase (x : vs) mdefault
  return $ makeBranch selector jumpList defaultJump
virtualDecision _ (DecisionSwap _ _) = undefined
virtualDecision [] t =
  lift $ throwE $ "virtualDecision. Note: \n" ++ Pr.ppShow t

virtualCase ::
     [Identifier]
  -> [(Identifier, Decision PreComp)]
  -> WithEnv [(Identifier, Identifier)]
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
virtualDefaultCase vs (Just (Nothing, tree)) = do
  code <- virtualDecision vs tree
  codeRef <- liftIO $ newIORef code
  label <- newName
  insCodeEnv label codeRef
  return $ Just (Nothing, label)
virtualDefaultCase vs (Just (Just x, tree)) = do
  code <- virtualDecision vs tree
  codeRef <- liftIO $ newIORef code
  label <- newName
  insCodeEnv label codeRef
  return $ Just (Just x, label)

type JumpList = [(Identifier, Identifier)]

makeBranch ::
     UData
  -> [(Identifier, Identifier)]
  -> Maybe (Maybe Identifier, Identifier)
  -> UCode
makeBranch _ [] Nothing = error "empty branch"
makeBranch d js@((_, target):_) Nothing = do
  Fix $ CodeSwitch d target js
makeBranch d js (Just (Just x, label)) = do
  Fix $ CodeLet x d (Fix $ CodeSwitch (Fix $ DataPointer x) label js)
makeBranch d js (Just (Nothing, label)) = do
  Fix $ CodeSwitch d label js

letSeq :: [UData] -> [Identifier] -> UCode -> UCode
letSeq [] [] code         = code
letSeq (d:ds) (i:is) code = Fix $ CodeLet i d (letSeq ds is code)
letSeq _ _ _              = error "Virtual.letSeq: invalid arguments"

traceLet :: String -> UCode -> UCode -> WithEnv UCode
traceLet s (Fix (CodeReturn o)) cont = return $ Fix $ CodeLet s o cont
traceLet s (Fix (CodeJump addr j args)) cont = do
  liftIO $ putStrLn $ "Found CodeJump with Let. The ident is " ++ show j ++ "."
  corresondingThunk <- lookupThunkEnv j
  case corresondingThunk of
    [i] -> do
      let newName = "thunk" ++ i ++ "unthunk" ++ j
      appendCode s cont newName
      return $ Fix $ CodeJump addr newName args
    [] -> return $ Fix $ CodeCall s addr args cont -- non-tail call
    _ ->
      lift $
      throwE $
      "multiple thunk found for an unthunk: \n" ++ show corresondingThunk
traceLet s (Fix (CodeLet k o1 o2)) cont = do
  c <- traceLet s o2 cont
  return $ Fix $ CodeLet k o1 c
traceLet s (Fix (CodeCall k i args o)) cont = do
  c <- traceLet s o cont
  return $ Fix $ CodeCall k i args c
traceLet s (Fix (switcher@(CodeSwitch _ defaultBranch branchList))) cont = do
  appendCode s cont defaultBranch
  forM_ branchList $ \(_, label) -> appendCode s cont label
  return $ Fix $ switcher

appendCode :: Identifier -> UCode -> Identifier -> WithEnv ()
appendCode s cont key = do
  mcode <- lookupCodeEnv key
  case mcode of
    Nothing -> lift $ throwE $ "no such code: " ++ show key
    Just coderef -> do
      code <- liftIO $ readIORef coderef
      code' <- traceLet s code cont
      liftIO $ writeIORef coderef code'

forallArgs :: CompType -> [Identifier]
forallArgs (CompTypeForall (i, _) t) = i : forallArgs t
forallArgs _                         = []

traceLowType :: [Int] -> LowType -> LowType
traceLowType [] t = t
traceLowType (i:is) (LowTypeVec _ args)
  | 0 <= i - 1 && i - 1 < length args = traceLowType is (args !! (i - 1))
traceLowType _ _ = LowTypeNull
