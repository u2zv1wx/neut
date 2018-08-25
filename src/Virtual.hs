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

virtual :: Term -> WithEnv Data
virtual (_ :< TermVar x) = do
  return $ DataPointer x
-- virtual (i :< ValueNodeApp s vs) = do
--   t <- lookupValueTypeEnv' i
--   case t of
--     ValueTypeNode node _ -> do
--       vs' <- mapM (virtual . Value) vs
--       i <- getConstructorNumber node s
--       return $ DataCell s i vs'
--     _ -> lift $ throwE $ "virtual.ValueNodeApp"
virtual (thunkId :< TermThunk comp) = do
  undefined -- asm <- virtual comp
  -- unthunkIdList <- lookupThunkEnv thunkId
  -- forM_ unthunkIdList $ \unthunkId -> do
  --   let label = "thunk" ++ thunkId ++ "unthunk" ++ unthunkId
  --   asmRef <- liftIO $ newIORef asm
  --   insCurrentCodeEnv label asmRef
  -- asmRef <- liftIO $ newIORef asm
  -- insCurrentCodeEnv ("thunk." ++ thunkId) asmRef -- just for completeness
  -- return $ DataLabel $ "thunk." ++ thunkId
virtual (_ :< TermLam _ comp) = do
  virtual comp
virtual app@(_ :< TermApp _ _) = do
  (cont, xs, vs) <- toFunAndArgs app
  ds <- mapM virtual vs
  cont' <- virtual cont
  undefined
  -- return $ CodeWithArg (zip xs ds) cont'
virtual (_ :< TermLift v) = do
  ans <- virtual v
  undefined
  -- return $ CodeReturn ans
virtual (_ :< TermBind s comp1 comp2) = do
  operation1 <- virtual comp1
  operation2 <- virtual comp2
  undefined
  -- traceLet s operation1 operation2
virtual (unthunkId :< TermUnthunk v) = do
  operand <- virtual v
  undefined
  -- case operand of
  --   DataPointer x -> do
  --     liftIO $ putStrLn $ "looking for thunk by unthunkId: " ++ show unthunkId
  --     thunkIdList <- lookupThunkEnv unthunkId
  --     liftIO $ putStrLn $ "found: " ++ show thunkIdList
  --     case thunkIdList of
  --       [] -> do
  --         return $ CodeRecursiveJump x
  --       [thunkId] -> do
  --         let label = "thunk" ++ thunkId ++ "unthunk" ++ unthunkId
  --         return $ CodeJump label
  --       _ -> do
  --         return $ CodeIndirectJump x unthunkId thunkIdList -- indirect branch
  --   DataLabel thunkId -> do
  --     let label = "thunk" ++ thunkId ++ "unthunk" ++ unthunkId
  --     return $ CodeJump label -- direct branch
  --   _ -> lift $ throwE "virtual.CompUnthunk"
virtual (_ :< TermMu s comp) = do
  current <- getScope
  setScope s
  insEmptyCodeEnv s
  asm <- virtual comp
  asm' <- liftIO $ newIORef asm
  undefined
  -- insCodeEnv s s asm'
  -- setScope current
  -- return $ CodeRecursiveJump s
virtual (_ :< TermDecision vs tree) = do
  fooList <-
    forM vs $ \v -> do
      asm <- virtual v
      i <- newNameWith "seq"
      return (i, asm)
  let (is, asms) = unzip fooList
  undefined
  -- body <- virtualDecision is tree
  -- letSeq is asms body

virtualDecision :: [Identifier] -> Decision Term -> WithEnv Code
virtualDecision asmList (DecisionLeaf ois preComp) = do
  let indexList = map fst ois
  let forEach = flip map
  let varList = map snd ois
  asmList' <-
    forM (zip asmList ois) $ \(x, (index, _)) -> do
      return $ DataElemAtIndex x index
  body <- virtual preComp
  letSeq varList asmList' body
virtualDecision (x:vs) (DecisionSwitch o cs mdefault) = do
  jumpList <- virtualase (x : vs) cs
  defaultJump <- virtualDefaultCase (x : vs) mdefault
  makeBranch x o jumpList defaultJump
virtualDecision _ (DecisionSwap _ _) = undefined
virtualDecision [] t =
  lift $ throwE $ "virtualDecision. Note: \n" ++ Pr.ppShow t

virtualase ::
     [Identifier]
  -> [((Identifier, Int), Decision Term)]
  -> WithEnv [(Identifier, Int, Identifier)]
virtualase _ [] = return []
virtualase vs (((cons, num), tree):cs) = do
  code <- virtualDecision vs tree
  label <- newNameWith cons
  codeRef <- liftIO $ newIORef code
  insCurrentCodeEnv label codeRef
  jumpList <- virtualase vs cs
  return $ (cons, num, label) : jumpList

virtualDefaultCase ::
     [Identifier]
  -> Maybe (Maybe Identifier, Decision Term)
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

toFunAndArgs :: Term -> WithEnv (Term, [Identifier], [Term])
toFunAndArgs c@(_ :< TermApp e@((i :< _)) v) = do
  t <- lookupTypeEnv' i
  case t of
    Fix (TypeForall (i, _) _) -> do
      (fun, xs, args) <- toFunAndArgs e
      return (fun, xs ++ [i], args ++ [v])
    _ -> return (c, [], [])
toFunAndArgs c = return (c, [], [])
