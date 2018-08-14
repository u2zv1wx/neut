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
virtualC app@(Comp (_ :< CompApp _ _)) = do
  let (cont, xs, vs) = toFunAndArgs app
  ds <- mapM virtualV vs
  cont' <- virtualC cont
  addMeta $ CodeWithArg xs ds cont'
virtualC (Comp (_ :< CompRet v)) = do
  ans <- virtualV v
  linkReg <- getLinkRegister
  addMeta $ CodeReturn linkReg ans
virtualC (Comp (_ :< CompBind s c1 c2)) = do
  operation1 <- virtualC (Comp c1)
  operation2 <- virtualC (Comp c2)
  traceLet s operation1 operation2
virtualC (Comp (_ :< CompUnthunk v@(Value (VMeta {vtype = ValueTypeDown tct} :< _)) j)) = do
  operand <- virtualV v
  let args = forallArgs tct
  case operand of
    Fix (DataPointer x) -> addMeta $ CodeIndirectJump x -- indirect branch
    Fix (DataLabel _)   -> addMeta $ CodeJump j -- direct branch
    _                   -> lift $ throwE "virtualC.CompUnthunk"
virtualC (Comp (_ :< CompUnthunk (Value (VMeta {vtype = _} :< _)) _)) = do
  lift $ throwE "virtualC.CompUnthunk"
virtualC (Comp (_ :< CompMu s c)) = do
  asm <- (virtualC $ Comp c)
  insCodeEnv s asm
  addMeta $ CodeJump s
virtualC (Comp (_ :< CompCase vs tree)) = do
  fooList <-
    forM vs $ \v -> do
      asm <- virtualV v
      i <- newName
      return (i, asm)
  let (is, asms) = unzip fooList
  body <- virtualDecision is tree
  letSeq is asms body

virtualApp :: Comp -> [Identifier] -> [Value] -> WithEnv Code
virtualApp cont xs vs = do
  ds <- mapM virtualV vs
  cont' <- virtualC cont
  letSeq xs ds cont'

addMeta :: PreCode -> WithEnv Code
addMeta pc = do
  meta <- emptyCodeMeta
  return $ meta :< pc

toFunAndArgs :: Comp -> (Comp, [Identifier], [Value])
toFunAndArgs (Comp (_ :< CompApp e@((CMeta {ctype = CompTypeForall (i, _) _} :< _)) v)) = do
  let (fun, xs, args) = toFunAndArgs (Comp e)
  (fun, xs ++ [i], args ++ [v])
toFunAndArgs c = (c, [], [])

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
  label <- newName
  insCodeEnv label code
  return $ Just (Nothing, label)
virtualDefaultCase vs (Just (Just x, tree)) = do
  code <- virtualDecision vs tree
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

letSeq :: [Identifier] -> [UData] -> Code -> WithEnv Code
letSeq [] [] code = return code
letSeq (i:is) (d:ds) code = do
  tmp <- letSeq is ds code
  addMeta $ CodeLet i d tmp
letSeq _ _ _ = error "Virtual.letSeq: invalid arguments"

traceLet :: String -> Code -> Code -> WithEnv Code
traceLet s (_ :< (CodeReturn _ ans)) cont = addMeta $ CodeLet s ans cont
traceLet s (_ :< (CodeJump addr)) cont = do
  traceLetJump s addr cont
traceLet s (_ :< (CodeIndirectJump addrInReg)) cont = do
  regName <- newName
  cont' <- traceLetJump s regName cont
  addMeta $ CodeLoad regName addrInReg cont'
traceLet s (_ :< (CodeLet k o1 o2)) cont = do
  c <- traceLet s o2 cont
  addMeta $ CodeLet k o1 c
traceLet s (_ :< (switcher@(CodeSwitch _ defaultBranch branchList))) cont = do
  appendCode s cont defaultBranch
  forM_ branchList $ \(_, label) -> appendCode s cont label
  addMeta $ switcher
traceLet s (_ :< (CodeWithArg xs ds body)) cont = do
  tmp <- traceLet s body cont
  case tmp of
    item@(_ :< CodeWithLinkReg _ _ _) -> do
      item' <- letSeq xs ds item -- set arguments
      withStackSave item' -- save stack before the preparation of arguments
    item -> letSeq xs ds item
traceLet _ _ _ = error "Virtual.traceLet" -- load/store

-- let s := (Jump addr) in cont
traceLetJump :: Identifier -> Identifier -> Code -> WithEnv Code
traceLetJump s addr cont = do
  thunkIdList <- lookupThunkEnv addr
  case thunkIdList of
    [i] -> do
      let newName = "thunk" ++ i ++ "unthunk" ++ addr
      appendCode s cont newName -- append (let s := <ans> in cont) to the code in codeEnv
      addMeta $ CodeJump newName -- ... and jump to that rewritten code
    [] -> do
      retLabelName <- newName -- create a new label to call back after jump
      cont' <- withStackRestore cont
      insCodeEnv retLabelName cont'
      jump <- addMeta $ CodeJump retLabelName
      linkReg <- getLinkRegister
      let retLabel = Fix $ DataLabel retLabelName
      addMeta $ CodeWithLinkReg linkReg retLabel jump -- set return address before jump
    _ ->
      lift $
      throwE $ "multiple thunk found for an unthunk: \n" ++ show thunkIdList

withStackSave :: Code -> WithEnv Code
withStackSave code = undefined

withStackRestore :: Code -> WithEnv Code
withStackRestore code = undefined

appendCode :: Identifier -> Code -> Identifier -> WithEnv ()
appendCode s cont key = do
  codeRef <- lookupFunEnv key
  code <- liftIO $ readIORef codeRef
  code' <- traceLet s code cont
  liftIO $ writeIORef codeRef code'

forallArgs :: CompType -> [Identifier]
forallArgs (CompTypeForall (i, _) t) = i : forallArgs t
forallArgs _                         = []
