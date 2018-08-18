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

virtualV :: Value -> WithEnv Data
virtualV (Value (_ :< ValueVar x)) = do
  return $ DataPointer x
virtualV (Value (VMeta {vtype = ValueTypeNode node _} :< ValueNodeApp s vs)) = do
  vs' <- mapM (virtualV . Value) vs
  i <- getConstructorNumber node s
  return $ DataCell s i vs'
virtualV (Value (_ :< ValueNodeApp _ _)) = do
  lift $ throwE $ "virtualV.ValueNodeApp"
virtualV (Value (_ :< ValueThunk comp thunkId)) = do
  asm <- virtualC comp
  unthunkIdList <- lookupThunkEnv thunkId
  forM_ unthunkIdList $ \unthunkId -> do
    let label = "thunk" ++ thunkId ++ "unthunk" ++ unthunkId
    asmRef <- liftIO $ newIORef asm
    insCurrentCodeEnv label asmRef
  asmRef <- liftIO $ newIORef asm
  insCurrentCodeEnv ("thunk." ++ thunkId) asmRef -- just for completeness
  return $ DataLabel $ "thunk." ++ thunkId

virtualC :: Comp -> WithEnv Code
virtualC (Comp (_ :< CompLam _ comp)) = do
  virtualC (Comp comp)
virtualC app@(Comp (_ :< CompApp _ _)) = do
  let (cont, xs, vs) = toFunAndArgs app
  ds <- mapM virtualV vs
  cont' <- virtualC cont
  return $ CodeWithArg (zip xs ds) cont'
virtualC (Comp (_ :< CompRet v)) = do
  ans <- virtualV v
  -- retReg <- getReturnRegister
  return $ CodeReturn ans
virtualC (Comp (_ :< CompBind s comp1 comp2)) = do
  operation1 <- virtualC (Comp comp1)
  operation2 <- virtualC (Comp comp2)
  traceLet s operation1 operation2
virtualC (Comp (_ :< CompUnthunk v unthunkId)) = do
  operand <- virtualV v
  case operand of
    DataPointer x -> do
      liftIO $ putStrLn $ "looking for thunk by unthunkId: " ++ show unthunkId
      thunkIdList <- lookupThunkEnv unthunkId
      liftIO $ putStrLn $ "found: " ++ show thunkIdList
      case thunkIdList of
        [] -> do
          return $ CodeRecursiveJump x
        [thunkId] -> do
          let label = "thunk" ++ thunkId ++ "unthunk" ++ unthunkId
          return $ CodeJump label
        _ -> do
          return $ CodeIndirectJump x unthunkId thunkIdList -- indirect branch
    DataLabel thunkId -> do
      let label = "thunk" ++ thunkId ++ "unthunk" ++ unthunkId
      return $ CodeJump label -- direct branch
    _ -> lift $ throwE "virtualC.CompUnthunk"
virtualC (Comp (_ :< CompMu s comp)) = do
  current <- getScope
  setScope s
  insEmptyCodeEnv s
  asm <- (virtualC $ Comp comp)
  asm' <- liftIO $ newIORef asm
  insCodeEnv s s asm'
  setScope current
  return $ CodeRecursiveJump s
virtualC (Comp (_ :< CompCase vs tree)) = do
  fooList <-
    forM vs $ \v -> do
      asm <- virtualV v
      i <- newNameWith "seq"
      return (i, asm)
  let (is, asms) = unzip fooList
  body <- virtualDecision is tree
  letSeq is asms body

virtualDecision :: [Identifier] -> Decision PreComp -> WithEnv Code
virtualDecision asmList (DecisionLeaf ois preComp) = do
  let indexList = map fst ois
  let forEach = flip map
  let varList = map (fst . snd) ois
  asmList' <-
    forM (zip asmList ois) $ \(x, ((index, _), _)) -> do
      return $ DataElemAtIndex x index
  body <- virtualC $ Comp preComp
  letSeq varList asmList' body
virtualDecision (x:vs) (DecisionSwitch (o, _) cs mdefault) = do
  jumpList <- virtualCase (x : vs) cs
  defaultJump <- virtualDefaultCase (x : vs) mdefault
  makeBranch x o jumpList defaultJump
virtualDecision _ (DecisionSwap _ _) = undefined
virtualDecision [] t =
  lift $ throwE $ "virtualDecision. Note: \n" ++ Pr.ppShow t

virtualCase ::
     [Identifier]
  -> [((Identifier, Int), Decision PreComp)]
  -> WithEnv [(Identifier, Int, Identifier)]
virtualCase _ [] = return []
virtualCase vs (((cons, num), tree):cs) = do
  code <- virtualDecision vs tree
  label <- newNameWith cons
  codeRef <- liftIO $ newIORef code
  insCurrentCodeEnv label codeRef
  jumpList <- virtualCase vs cs
  return $ (cons, num, label) : jumpList

virtualDefaultCase ::
     [Identifier]
  -> Maybe (Maybe Identifier, Decision PreComp)
  -> WithEnv (Maybe (Maybe Identifier, Identifier))
virtualDefaultCase _ Nothing = return Nothing
virtualDefaultCase vs (Just (Nothing, tree)) = do
  codeRef <- virtualDecision vs tree >>= liftIO . newIORef
  label <- newNameWith "default"
  insCurrentCodeEnv label codeRef
  return $ Just (Nothing, label)
virtualDefaultCase vs (Just (Just x, tree)) = do
  codeRef <- virtualDecision vs tree >>= liftIO . newIORef
  label <- newNameWith $ "default-" ++ x
  insCurrentCodeEnv label codeRef
  return $ Just (Just x, label)

type JumpList = [(Identifier, Identifier)]

makeBranch ::
     Identifier
  -> Index
  -> [(Identifier, Int, Identifier)]
  -> Maybe (Maybe Identifier, Identifier)
  -> WithEnv Code
makeBranch _ _ [] Nothing = error "empty branch"
makeBranch y o js@((_, _, target):_) Nothing = do
  if null o
    then return $ (CodeSwitch y target js)
    else do
      let tmp = DataElemAtIndex y o
      name <- newName
      let tmp2 = (CodeSwitch name target js)
      return $ CodeLet name tmp tmp2
makeBranch y o js (Just (Just defaultName, label)) = do
  if null o
    then return $ (CodeSwitch y label js)
    else do
      let tmp = CodeSwitch defaultName label js
      return $ CodeLet defaultName (DataElemAtIndex y o) tmp
makeBranch y o js (Just (Nothing, label)) = do
  if null o
    then return $ (CodeSwitch y label js)
    else do
      let tmp = DataElemAtIndex y o
      name <- newName
      let tmp2 = CodeSwitch name label js
      return $ CodeLet name tmp tmp2

traceLet :: String -> Code -> Code -> WithEnv Code
traceLet s (CodeReturn ans) cont = return $ CodeLet s ans cont
traceLet s (CodeJump label) cont = do
  appendCode s cont label
  return $ CodeJump label
traceLet s c@(CodeRecursiveJump _) cont = do
  traceLet s (CodeWithArg [] c) cont
traceLet s (CodeIndirectJump addrInReg unthunkId poss) cont = do
  forM_ poss $ \thunkId -> do
    let label = "thunk" ++ thunkId ++ "unthunk" ++ unthunkId -- unthunkId
    appendCode s cont label
  return $ CodeIndirectJump addrInReg unthunkId poss
traceLet s (switcher@(CodeSwitch _ defaultBranch branchList)) cont = do
  appendCode s cont defaultBranch
  forM_ branchList $ \(_, _, label) -> appendCode s cont label
  return $ switcher
traceLet s (CodeLet k o1 o2) cont = do
  c <- traceLet s o2 cont
  return $ CodeLet k o1 c
traceLet s (CodeLetLink linkReg linkLabel body) cont = do
  c <- traceLet s body cont
  return $ CodeLetLink linkReg linkLabel c
traceLet s (CodeWithArg xds code) cont =
  case code of
    CodeRecursiveJump name -> return $ CodeCall s name xds cont
    _ -> do
      tmp <- traceLet s code cont
      let (xs, ds) = unzip xds
      letSeq xs ds tmp
traceLet s (CodeCall reg name xds cont1) cont2 = do
  tmp <- traceLet s cont1 cont2
  return $ CodeCall reg name xds tmp

appendCode :: Identifier -> Code -> Identifier -> WithEnv ()
appendCode s cont key = do
  current <- getScope
  codeRef <- lookupCodeEnv2 current key -- key is the target of jump
  code <- liftIO $ readIORef codeRef
  code' <- traceLet s code cont
  liftIO $ writeIORef codeRef code'

forallArgs :: CompType -> [Identifier]
forallArgs (CompTypeForall (i, _) t) = i : forallArgs t
forallArgs _                         = []

toFunAndArgs :: Comp -> (Comp, [Identifier], [Value])
toFunAndArgs (Comp (_ :< CompApp e@((CMeta {ctype = CompTypeForall (i, _) _} :< _)) v)) = do
  let (fun, xs, args) = toFunAndArgs (Comp e)
  (fun, xs ++ [i], args ++ [v])
toFunAndArgs c = (c, [], [])
