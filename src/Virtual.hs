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
virtualV (Value (_ :< ValueNodeApp s vs)) = do
  vs' <- mapM (virtualV . Value) vs
  return $ Fix $ DataCell s vs'
virtualV (Value (_ :< ValueThunk comp thunkId)) = do
  asm <- virtualC comp
  unthunkIdList <- lookupThunkEnv thunkId
  forM_ unthunkIdList $ \unthunkId -> do
    let label = "thunk" ++ thunkId ++ "unthunk" ++ unthunkId
    insCodeEnv label asm
  return $ Fix $ DataLabel thunkId

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
  linkReg <- getLinkRegister
  retReg <- getReturnRegister
  addMeta $ CodeReturn retReg linkReg ans
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
        [thunkId] -> do
          let label = "thunk" ++ thunkId ++ "unthunk" ++ unthunkId
          addMeta $ CodeJump label
        _ -> do
          let possibleJumps = map (\x -> "thunk" ++ x) thunkIdList
          addMeta $ CodeIndirectJump x possibleJumps -- indirect branch
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
      return $ Fix $ DataElemAtIndex (Fix $ DataPointer x) index
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
  -> [(Identifier, Decision PreComp)]
  -> WithEnv [(Identifier, Identifier)]
virtualCase _ [] = return []
virtualCase vs ((cons, tree):cs) = do
  code <- virtualDecision vs tree
  label <- newNameWith cons
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
  -> [(Identifier, Identifier)]
  -> Maybe (Maybe Identifier, Identifier)
  -> WithEnv Code
makeBranch _ _ [] Nothing = error "empty branch"
makeBranch y o js@((_, target):_) Nothing = do
  if null o
    then addMeta $ (CodeSwitch y target js)
    else do
      let tmp = Fix $ DataElemAtIndex (Fix $ DataPointer y) o
      name <- newName
      tmp2 <- addMeta $ (CodeSwitch name target js)
      addMeta $ CodeLet name tmp tmp2
makeBranch y o js (Just (Just defaultName, label)) = do
  if null o
    then addMeta $ (CodeSwitch y label js)
    else do
      tmp <- addMeta $ CodeSwitch defaultName label js
      addMeta $
        CodeLet defaultName (Fix $ DataElemAtIndex (Fix $ DataPointer y) o) tmp
makeBranch y o js (Just (Nothing, label)) = do
  if null o
    then addMeta $ (CodeSwitch y label js)
    else do
      let tmp = Fix $ DataElemAtIndex (Fix $ DataPointer y) o
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
traceLet s (_ :< (CodeIndirectJump addrInReg poss)) cont = do
  retReg <- getReturnRegister
  cont' <- withStackRestore cont
  cont'' <- addMeta $ CodeLet s (Fix $ DataPointer retReg) cont'
  linkLabelName <- newNameWith $ "cont-for-" ++ addrInReg
  insCodeEnv linkLabelName cont''
  linkReg <- getLinkRegister
  let linkLabel = Fix $ DataLabel linkLabelName
  jumpToAddr <- addMeta $ CodeIndirectJump addrInReg poss
  addMeta $ CodeLetLink linkReg linkLabel jumpToAddr
traceLet s (_ :< (switcher@(CodeSwitch _ defaultBranch branchList))) cont = do
  appendCode s cont defaultBranch
  forM_ branchList $ \(_, label) -> appendCode s cont label
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

-- traceLetJump :: Identifier -> Identifier -> Code -> WithEnv Code
-- traceLetJump s addr cont = do
--   liftIO $ putStrLn $ "looking for thunk of name " ++ show addr
--   thunkIdList <- lookupThunkEnv addr
--   case thunkIdList of
--     [i] -> do
--       let newName = "thunk" ++ i ++ "unthunk" ++ addr
--       appendCode s cont newName -- append (let s := <ans> in cont) to the code in codeEnv
--       addMeta $ CodeJump newName -- ... and jump to that rewritten code
--     [] -> do
--       retReg <- getReturnRegister
--       cont' <- withStackRestore cont
--       cont'' <- addMeta $ CodeLet s (Fix $ DataPointer retReg) cont'
--       linkLabelName <- newNameWith $ "cont-for-" ++ addr
--       insCodeEnv linkLabelName cont''
--       linkReg <- getLinkRegister
--       let linkLabel = Fix $ DataLabel linkLabelName
--       jumpToAddr <- addMeta $ CodeJump addr
--       addMeta $ CodeLetLink linkReg linkLabel jumpToAddr
--     _ ->
--       lift $
--       throwE $ "multiple thunk found for an unthunk: \n" ++ show thunkIdList
appendCode :: Identifier -> Code -> Identifier -> WithEnv ()
appendCode s cont key = do
  codeRef <- lookupFunEnv key
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

withStackSave :: Code -> WithEnv Code
withStackSave code = do
  stackReg <- getStackRegister
  addMeta $ CodeStackSave stackReg code

withStackRestore :: Code -> WithEnv Code
withStackRestore code = do
  stackReg <- getStackRegister
  addMeta $ CodeStackRestore stackReg code
