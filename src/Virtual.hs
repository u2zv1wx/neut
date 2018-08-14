module Virtual where

import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.IORef

import           Data

import           Control.Comonad.Cofree

import qualified Text.Show.Pretty           as Pr

import           Debug.Trace

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
    insCodeEnv newName asm
  return $ Fix $ DataLabel i

virtualC :: Comp -> WithEnv Code
virtualC (Comp (_ :< CompLam _ e)) = do
  virtualC (Comp e)
virtualC (Comp (_ :< CompApp e@(CMeta {ctype = ect} :< _) v)) = do
  case ect of
    CompTypeForall (i, _) _ -> do
      v' <- virtualV v
      e' <- virtualC (Comp e)
      addMeta $ CodeLet i v' e'
    _ -> do
      lift $ throwE $ "virtualC.CompApp. Note:\n " ++ Pr.ppShow ect
virtualC (Comp (_ :< CompRet v)) = do
  asm <- virtualV v
  addMeta $ CodeReturn asm
virtualC (Comp (_ :< CompBind s c1 c2)) = do
  operation1 <- virtualC (Comp c1)
  operation2 <- virtualC (Comp c2)
  traceLet s operation1 operation2
virtualC (Comp (_ :< CompUnthunk v@(Value (VMeta {vtype = ValueTypeDown tct} :< _)) j)) = do
  operand <- virtualV v
  let args = forallArgs tct
  case operand of
    Fix (DataPointer _) -> addMeta $ CodeIndirectJump j args -- indirect branch
    Fix (DataLabel _)   -> addMeta $ CodeJump j args -- direct branch
    _                   -> lift $ throwE "virtualC.CompUnthunk"
virtualC (Comp (_ :< CompUnthunk (Value (VMeta {vtype = _} :< _)) _)) = do
  lift $ throwE "virtualC.CompUnthunk"
virtualC (Comp (CMeta {ctype = ct} :< CompMu s c)) = do
  asm <- (virtualC $ Comp c)
  insCodeEnv s asm
  addMeta $ CodeJump s (forallArgs ct)
virtualC (Comp (_ :< CompCase vs tree)) = do
  fooList <-
    forM vs $ \v -> do
      asm <- virtualV v
      i <- newName
      return (i, asm)
  let (is, asms) = unzip fooList
  body <- virtualDecision is tree
  letSeq asms is body

addMeta :: PreCode -> WithEnv Code
addMeta pc = do
  meta <- emptyCodeMeta
  return $ meta :< pc

virtualDecision :: [Identifier] -> Decision PreComp -> WithEnv Code
virtualDecision asmList (DecisionLeaf ois preComp) = do
  let indexList = map fst ois
  let forEach = flip map
  let varList = map (fst . snd) ois
  asmList' <-
    forM (zip asmList ois) $ \(x, ((index, _), _)) -> do
      return $ Fix $ DataElemAtIndex (Fix $ DataPointer x) index
  body <- virtualC $ Comp preComp
  letSeq asmList' varList body
virtualDecision (x:vs) (DecisionSwitch (o, _) cs mdefault) = do
  let selector = Fix $ DataElemAtIndex (Fix $ DataPointer x) o
  jumpList <- virtualCase (x : vs) cs
  defaultJump <- virtualDefaultCase (x : vs) mdefault
  makeBranch selector jumpList defaultJump
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
  -- codeRef <- liftIO $ newIORef code
  label <- newName
  insCodeEnv label code
  jumpList <- virtualCase vs cs
  return $ (cons, label) : jumpList

virtualDefaultCase ::
     [Identifier]
  -> Maybe (Maybe Identifier, Decision PreComp)
  -> WithEnv (Maybe (Maybe Identifier, Identifier))
virtualDefaultCase _ Nothing = return Nothing
virtualDefaultCase vs (Just (Nothing, tree)) = do
  code <- virtualDecision vs tree
  -- codeRef <- liftIO $ newIORef code
  label <- newName
  insCodeEnv label code
  return $ Just (Nothing, label)
virtualDefaultCase vs (Just (Just x, tree)) = do
  code <- virtualDecision vs tree
  -- codeRef <- liftIO $ newIORef $ code
  label <- newName
  insCodeEnv label code
  return $ Just (Just x, label)

type JumpList = [(Identifier, Identifier)]

makeBranch ::
     UData
  -> [(Identifier, Identifier)]
  -> Maybe (Maybe Identifier, Identifier)
  -> WithEnv Code
makeBranch _ [] Nothing = error "empty branch"
makeBranch d js@((_, target):_) Nothing = do
  addMeta $ CodeSwitch d target js
makeBranch d js (Just (Just x, label)) = do
  tmp <- addMeta $ CodeSwitch (Fix $ DataPointer x) label js
  addMeta $ CodeLet x d tmp
makeBranch d js (Just (Nothing, label)) = do
  addMeta $ CodeSwitch d label js

letSeq :: [UData] -> [Identifier] -> Code -> WithEnv Code
letSeq [] [] code = return code
letSeq (d:ds) (i:is) code = do
  tmp <- letSeq ds is code
  addMeta $ CodeLet i d tmp
letSeq _ _ _ = error "Virtual.letSeq: invalid arguments"

traceLet :: String -> Code -> Code -> WithEnv Code
traceLet s (_ :< (CodeReturn o)) cont = addMeta $ CodeLet s o cont
traceLet s (_ :< (CodeJump j args)) cont = do
  liftIO $ putStrLn $ "Found CodeJump with Let. The ident is " ++ show j ++ "."
  corresondingThunk <- lookupThunkEnv j
  case corresondingThunk of
    [i] -> do
      let newName = "thunk" ++ i ++ "unthunk" ++ j
      appendCode s cont newName
      addMeta $ CodeJump newName args
    [] -> addMeta $ CodeCall s j args cont -- non-tail call
    _ ->
      lift $
      throwE $
      "multiple thunk found for an unthunk: \n" ++ show corresondingThunk
traceLet s (_ :< (CodeLet k o1 o2)) cont = do
  c <- traceLet s o2 cont
  addMeta $ CodeLet k o1 c
traceLet s (_ :< (CodeCall k i args o)) cont = do
  c <- traceLet s o cont
  addMeta $ CodeCall k i args c
traceLet s (_ :< (switcher@(CodeSwitch _ defaultBranch branchList))) cont = do
  appendCode s cont defaultBranch
  forM_ branchList $ \(_, label) -> appendCode s cont label
  addMeta $ switcher
traceLet _ _ _ = error "Virtual.traceLet" -- load/store

appendCode :: Identifier -> Code -> Identifier -> WithEnv ()
appendCode s cont key = do
  codeRef <- lookupFunEnv key
  code <- liftIO $ readIORef codeRef
  code' <- traceLet s code cont
  liftIO $ writeIORef codeRef code'

forallArgs :: CompType -> [Identifier]
forallArgs (CompTypeForall (i, _) t) = i : forallArgs t
forallArgs _                         = []

traceLowType :: [Int] -> LowType -> LowType
traceLowType [] t = t
traceLowType (i:is) (LowTypeVec _ args)
  | 0 <= i - 1 && i - 1 < length args = traceLowType is (args !! (i - 1))
traceLowType _ _ = LowTypeNull
