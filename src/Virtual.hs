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
virtualV (Value (_ :< ValueVar x)) = do
  return $ Fix (DataPointer x)
virtualV (Value (VMeta {vtype = ValueTypeNode node _} :< ValueNodeApp s vs)) = do
  vs' <- mapM (virtualV . Value) vs
  i <- getConstructorNumber node s
  return $ Fix $ DataCell s i vs'
virtualV (Value (_ :< ValueNodeApp _ _)) = do
  lift $ throwE $ "virtualV.ValueNodeApp"
virtualV (Value (_ :< ValueThunk comp thunkId)) = do
  asm <- virtualC comp
  unthunkIdList <- lookupThunkEnv thunkId
  forM_ unthunkIdList $ \unthunkId -> do
    let label = "thunk" ++ thunkId ++ "unthunk" ++ unthunkId
    insCodeEnv label asm
  insCodeEnv ("thunk" ++ thunkId) asm -- just for completeness
  return $ Fix $ DataLabel $ "thunk" ++ thunkId

virtualC :: Comp -> WithEnv Code
virtualC (Comp (_ :< CompLam _ comp)) = do
  virtualC (Comp comp)
virtualC app@(Comp (_ :< CompApp _ _)) = do
  let (cont, xs, vs) = toFunAndArgs app
  ds <- mapM virtualV vs
  _ :< cont' <- virtualC cont
  meta <- emptyCodeMeta
  return $ meta {codeMetaArgs = zip xs ds} :< cont'
virtualC (Comp (_ :< CompRet v)) = do
  ans <- virtualV v
  -- linkReg <- getLinkRegister
  retReg <- getReturnRegister
  addMeta $ CodeReturn retReg "exit" ans
virtualC (Comp (_ :< CompBind s comp1 comp2)) = do
  operation1 <- virtualC (Comp comp1)
  operation2 <- virtualC (Comp comp2)
  traceLet s operation1 operation2
virtualC (Comp (_ :< CompUnthunk v unthunkId)) = do
  operand <- virtualV v
  case operand of
    Fix (DataPointer x) -> do
      liftIO $ putStrLn $ "looking for thunk by unthunkId: " ++ show unthunkId
      thunkIdList <- lookupThunkEnv unthunkId
      liftIO $ putStrLn $ "found: " ++ show thunkIdList
      case thunkIdList of
        [] -> do
          addMeta $ CodeRecursiveJump x
        [thunkId] -> do
          let label = "thunk" ++ thunkId ++ "unthunk" ++ unthunkId
          addMeta $ CodeJump label
        _ -> do
          let possibleJumps = map (\x -> "thunk" ++ x) thunkIdList
          addMeta $ CodeIndirectJump x unthunkId possibleJumps -- indirect branch
    Fix (DataLabel thunkId) -> do
      let label = "thunk" ++ thunkId ++ "unthunk" ++ unthunkId
      addMeta $ CodeJump label -- direct branch
    _ -> lift $ throwE "virtualC.CompUnthunk"
virtualC (Comp (_ :< CompMu s comp)) = do
  asm <- (virtualC $ Comp comp)
  insCodeEnv s asm
  addMeta $ CodeJump s
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
      return $ Fix $ DataElemAtIndex x index
  body <- virtualC $ Comp preComp
  letSeq varList asmList' body
virtualDecision (x:vs) (DecisionSwitch (o, _) cs mdefault) = do
  jumpList <- virtualCase (x : vs) cs
  defaultJump <- virtualDefaultCase (x : vs) mdefault
  makeBranch x o jumpList defaultJump
--  let selector = Fix $ DataElemAtIndex (Fix $ DataPointer x) o
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
  insCodeEnv label code
  jumpList <- virtualCase vs cs
  return $ (cons, num, label) : jumpList

virtualDefaultCase ::
     [Identifier]
  -> Maybe (Maybe Identifier, Decision PreComp)
  -> WithEnv (Maybe (Maybe Identifier, Identifier))
virtualDefaultCase _ Nothing = return Nothing
virtualDefaultCase vs (Just (Nothing, tree)) = do
  code <- virtualDecision vs tree
  label <- newNameWith "default"
  insCodeEnv label code
  return $ Just (Nothing, label)
virtualDefaultCase vs (Just (Just x, tree)) = do
  code <- virtualDecision vs tree
  label <- newNameWith $ "default-" ++ x
  insCodeEnv label code
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
    then addMeta $ (CodeSwitch y target js)
    else do
      let tmp = Fix $ DataElemAtIndex y o
      name <- newName
      tmp2 <- addMeta $ (CodeSwitch name target js)
      addMeta $ CodeLet name tmp tmp2
makeBranch y o js (Just (Just defaultName, label)) = do
  if null o
    then addMeta $ (CodeSwitch y label js)
    else do
      tmp <- addMeta $ CodeSwitch defaultName label js
      addMeta $ CodeLet defaultName (Fix $ DataElemAtIndex y o) tmp
makeBranch y o js (Just (Nothing, label)) = do
  if null o
    then addMeta $ (CodeSwitch y label js)
    else do
      let tmp = Fix $ DataElemAtIndex y o
      name <- newName
      tmp2 <- addMeta $ (CodeSwitch name label js)
      addMeta $ CodeLet name tmp tmp2

traceLet :: String -> Code -> Code -> WithEnv Code
traceLet s (CodeMeta {codeMetaArgs = xds@(_:_)} :< code) cont = do
  code' <- addMeta code
  tmp <- traceLet s code' cont
  case tmp of
    _ :< CodeLetLink _ _ _ -> do
      let (xs, ds) = unzip xds
      tmp' <- letSeq xs ds tmp
      withStackSave tmp'
    _ -> do
      let (xs, ds) = unzip xds
      letSeq xs ds tmp
traceLet s (_ :< (CodeReturn _ _ ans)) cont = addMeta $ CodeLet s ans cont
traceLet s (_ :< (CodeJump label)) cont = do
  appendCode s cont label
  addMeta $ CodeJump label
traceLet _ (_ :< (CodeRecursiveJump _)) _ = do
  undefined
traceLet s (_ :< (CodeIndirectJump addrInReg unthunkId poss)) cont = do
  retReg <- getReturnRegister
  cont' <- withStackRestore cont
  cont'' <- addMeta $ CodeLet s (Fix $ DataPointer retReg) cont'
  linkLabelName <- newNameWith $ "cont-for-" ++ addrInReg
  insCodeEnv linkLabelName cont''
  linkReg <- getLinkRegister
  let linkLabel = Fix $ DataLabel linkLabelName
  forM_ poss $ \thunkId -> do
    let label = "thunk" ++ thunkId ++ "unthunk" ++ unthunkId -- unthunkId
    codeRef <- lookupFunEnv label
    code <- liftIO $ readIORef codeRef
    code' <- updateReturnAddr linkLabelName code
    updateCodeEnv label code'
  jumpToAddr <- addMeta $ CodeIndirectJump addrInReg unthunkId poss
  addMeta $ CodeLetLink linkReg linkLabel jumpToAddr
traceLet s (_ :< (switcher@(CodeSwitch _ defaultBranch branchList))) cont = do
  appendCode s cont defaultBranch
  forM_ branchList $ \(_, _, label) -> appendCode s cont label
  addMeta $ switcher
traceLet s (_ :< (CodeLet k o1 o2)) cont = do
  c <- traceLet s o2 cont
  addMeta $ CodeLet k o1 c
traceLet s (_ :< (CodeLetLink linkReg linkLabel body)) cont = do
  c <- traceLet s body cont
  addMeta $ CodeLetLink linkReg linkLabel c
traceLet _ (_ :< (CodeStackSave _ _)) _ =
  error "stacksave at the tail of a term"
traceLet _ (_ :< (CodeStackRestore _ _)) _ =
  error "stackrestore at the tail of a term"

appendCode :: Identifier -> Code -> Identifier -> WithEnv ()
appendCode s cont key = do
  codeRef <- lookupFunEnv key
  code <- liftIO $ readIORef codeRef
  code' <- traceLet s code cont
  liftIO $ writeIORef codeRef code'

updateReturnAddr :: Identifier -> Code -> WithEnv Code
updateReturnAddr label (_ :< (CodeReturn retReg _ ans)) =
  addMeta $ CodeReturn retReg label ans
updateReturnAddr label (_ :< (CodeLet x d cont)) = do
  cont' <- updateReturnAddr label cont
  addMeta $ CodeLet x d cont'
updateReturnAddr label (_ :< (CodeLetLink x d cont)) = do
  cont' <- updateReturnAddr label cont
  addMeta $ CodeLetLink x d cont'
updateReturnAddr label (_ :< (CodeSwitch x defaultBranch branchList)) = do
  updateReturnAddr' label defaultBranch
  forM_ branchList $ \(_, _, br) -> updateReturnAddr' label br
  addMeta $ (CodeSwitch x defaultBranch branchList)
updateReturnAddr label (_ :< (CodeJump dest)) = do
  updateReturnAddr' label dest
  addMeta $ CodeJump dest
updateReturnAddr label (_ :< (CodeIndirectJump addrInReg unthunkId poss)) = do
  forM_ poss $ \thunkId -> do
    let codeLabel = "thunk" ++ thunkId ++ "unthunk" ++ unthunkId -- unthunkId
    codeRef <- lookupFunEnv codeLabel
    code <- liftIO $ readIORef codeRef
    code' <- updateReturnAddr label code
    updateCodeEnv codeLabel code'
  addMeta $ CodeIndirectJump addrInReg unthunkId poss
updateReturnAddr label (_ :< (CodeRecursiveJump x)) = do
  updateReturnAddr' label x
  addMeta $ CodeRecursiveJump x
updateReturnAddr _ (_ :< (CodeStackSave _ _)) = do
  error "stacksave at the tail of a term"
updateReturnAddr _ (_ :< (CodeStackRestore _ _)) = do
  error "stacksave at the tail of a term"

updateReturnAddr' :: Identifier -> Identifier -> WithEnv ()
updateReturnAddr' label key = do
  codeRef <- lookupFunEnv key
  code <- liftIO $ readIORef codeRef
  code' <- updateReturnAddr label code
  liftIO $ writeIORef codeRef code'

forallArgs :: CompType -> [Identifier]
forallArgs (CompTypeForall (i, _) t) = i : forallArgs t
forallArgs _                         = []

toFunAndArgs :: Comp -> (Comp, [Identifier], [Value])
toFunAndArgs (Comp (_ :< CompApp e@((CMeta {ctype = CompTypeForall (i, _) _} :< _)) v)) = do
  let (fun, xs, args) = toFunAndArgs (Comp e)
  (fun, xs ++ [i], args ++ [v])
toFunAndArgs c = (c, [], [])

withStackSave :: Code -> WithEnv Code
withStackSave code = do
  stackReg <- getStackRegister
  addMeta $ CodeStackSave stackReg code

withStackRestore :: Code -> WithEnv Code
withStackRestore code = do
  stackReg <- getStackRegister
  addMeta $ CodeStackRestore stackReg code
