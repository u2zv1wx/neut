module Virtual
  ( virtualV
  , virtualC
  ) where

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
virtualV (Value (i :< ValueVar x)) = return $ i :< DataLocal x
virtualV (Value (i :< ValueConst x)) = return $ i :< DataGlobal x
virtualV (Value (i :< ValueThunk comp)) = do
  let label = "thunk" ++ i
  thunkType <- lookupTypeEnv' i
  insTypeEnv label thunkType
  (body, args) <- toLamSeq comp
  bodyCode <- virtualC body
  insCodeEnv label args bodyCode
  return $ i :< DataGlobal label
virtualV (Value (i :< ValueProduct v1 v2)) = undefined

virtualC :: Comp -> WithEnv Code
virtualC lam@(Comp (lamMeta :< CompLam _ _))
  -- interpret (lambda x e) as !&(lambda x e).
 = do
  (body, args) <- toLamSeq lam
  bodyCode <- virtualC body
  name <- newNameWith "lam"
  lamType <- lookupTypeEnv' lamMeta
  insTypeEnv name $ Fix $ TypeDown lamType
  insCodeEnv name args bodyCode
  meta <- newNameWith "meta"
  insTypeEnv meta $ Fix $ TypeDown lamType
  return $ CodeLoad (meta :< DataGlobal name)
virtualC app@(Comp (i :< CompApp _ _)) = do
  (Comp (funMeta :< fun), ivs) <- funAndArgsPol app
  let (_, vs) = unzip ivs
  ds <- mapM virtualV vs
  funCode <- virtualC $ Comp (funMeta :< fun)
  funName <- newNameWith "fun"
  funType <- lookupTypeEnv' funMeta
  -- fun : P -> N
  -- funName : &(P -> N)
  insTypeEnv funName $ Fix (TypeDown funType)
  s <- newNameWith "tmp"
  resultType <- lookupTypeEnv' i
  insTypeEnv s $ Fix (TypeDown resultType)
  meta <- newNameWith "meta"
  insTypeEnv meta $ Fix (TypeDown resultType)
  case fun of
    CompBind x e1 e2 -> do
      let Comp e2' = coFunAndArgsPol (Comp e2, ivs)
      virtualC $ Comp $ i :< CompBind x e1 e2'
    CompDecision ds tree -> do
      let tree' = liftDecision (\x -> coFunAndArgsPol (Comp x, ivs)) tree
      let tree'' = liftDecision (\(Comp x) -> x) tree'
      virtualC $ Comp $ i :< CompDecision ds tree''
    CompMu x e -> do
      let Comp e' = coFunAndArgsPol (Comp e, ivs)
      virtualC $ Comp $ i :< CompMu x e'
    CompLift _ -> error "type error"
    CompApp _ _ -> error "unreachable"
    _ ->
      traceLet funName funCode $
      CodeCall s funName ds (CodeReturn (meta :< DataGlobal s))
virtualC (Comp (_ :< CompLift v)) = do
  ans <- virtualV v
  return $ CodeReturn ans
virtualC (Comp (_ :< CompBind s comp1 comp2)) = do
  operation1 <- virtualC (Comp comp1)
  operation2 <- virtualC (Comp comp2)
  traceLet s operation1 operation2
virtualC (Comp (_ :< CompUnthunk v)) = do
  asm <- virtualV v
  return $ CodeLoad asm
virtualC (Comp (_ :< CompMu s comp))
  -- interpret (mu x e) as !&(mu x e)
 = do
  asm <- virtualC $ Comp comp
  insCodeEnv s [] asm
  meta <- newNameWith "meta"
  recType <- lookupTypeEnv' s
  insTypeEnv meta recType
  return $ CodeLoad (meta :< DataGlobal s)
virtualC (Comp (_ :< CompDecision vs tree)) = do
  valueList <-
    forM vs $ \v@(Value (valueMeta :< _)) -> do
      asm <- virtualV v
      i <- newNameWith "seq"
      valueType <- lookupTypeEnv' valueMeta
      insTypeEnv i valueType
      return (i, asm)
  let (is, asms) = unzip valueList
  body <- virtualDecision is tree
  letSeq is asms body

virtualDecision :: [Identifier] -> Decision PreComp -> WithEnv Code
virtualDecision asmList (DecisionLeaf ois e) = do
  varAsmList <-
    forM (zip asmList ois) $ \(x, ((index, t), var)) -> do
      insTypeEnv var t
      meta <- newNameWith "meta"
      insTypeEnv meta t
      return (var, meta :< DataElemAtIndex x index)
  body <- virtualC $ Comp e
  let (varList, asmList) = unzip varAsmList
  letSeq varList asmList body
virtualDecision (x:vs) (DecisionSwitch o cs mdefault) = do
  jumpList <- virtualCase (x : vs) cs
  defaultJump <- virtualDefaultCase (x : vs) mdefault
  makeBranch x o jumpList defaultJump
virtualDecision _ (DecisionSwap _ _) = undefined
virtualDecision [] t =
  lift $ throwE $ "virtualDecision. Note: \n" ++ Pr.ppShow t

virtualCase ::
     [Identifier]
  -> [((Identifier, Int), Decision PreComp)]
  -> WithEnv [(Identifier, Int, Identifier, Code)]
virtualCase _ [] = return []
virtualCase vs (((cons, num), tree):cs) = do
  code <- virtualDecision vs tree
  label <- newNameWith cons
  jumpList <- virtualCase vs cs
  return $ (cons, num, label, code) : jumpList

virtualDefaultCase ::
     [Identifier]
  -> Maybe (Maybe Identifier, Decision PreComp)
  -> WithEnv (Maybe (Maybe Identifier, Identifier, Code))
virtualDefaultCase _ Nothing = return Nothing
virtualDefaultCase vs (Just (Nothing, tree)) = do
  code <- virtualDecision vs tree
  label <- newNameWith "default"
  return $ Just (Nothing, label, code)
virtualDefaultCase vs (Just (Just x, tree)) = do
  code <- virtualDecision vs tree
  label <- newNameWith $ "default-" ++ x
  return $ Just (Just x, label, code)

makeBranch ::
     Identifier
  -> Occurrence
  -> [(Identifier, Int, Identifier, Code)]
  -> Maybe (Maybe Identifier, Identifier, Code)
  -> WithEnv Code
makeBranch _ _ [] Nothing = error "empty branch"
makeBranch y (o, t) js@((_, _, target, code):_) Nothing =
  if null o
    then return (CodeSwitch y (target, code) js)
    else do
      name <- newName
      insTypeEnv name t
      meta <- newNameWith "meta"
      insTypeEnv meta t
      return $
        CodeLet name (meta :< DataElemAtIndex y o) $
        CodeSwitch name (target, code) js
makeBranch y (o, t) js (Just (Just defaultName, label, code)) =
  if null o
    then return (CodeSwitch y (label, code) js)
    else do
      insTypeEnv defaultName t
      meta <- newNameWith "meta"
      insTypeEnv meta t
      return $
        CodeLet defaultName (meta :< DataElemAtIndex y o) $
        CodeSwitch defaultName (label, code) js
makeBranch y (o, t) js (Just (Nothing, label, code)) =
  if null o
    then return (CodeSwitch y (label, code) js)
    else do
      name <- newName
      insTypeEnv name t
      meta <- newNameWith "meta"
      insTypeEnv meta t
      return $
        CodeLet name (meta :< DataElemAtIndex y o) $
        CodeSwitch name (label, code) js

traceLet :: String -> Code -> Code -> WithEnv Code
traceLet s (CodeReturn ans@(_ :< _)) cont = return $ CodeLet s ans cont
traceLet s (CodeSwitch x (label, defaultBranch) branchList) cont = do
  defaultBranch' <- traceLet s defaultBranch cont
  branchList' <-
    forM branchList $ \(name, id, label, code) -> do
      code' <- traceLet s code cont
      return (name, id, label, code')
  return $ CodeSwitch x (label, defaultBranch') branchList'
traceLet s (CodeLet k o1 o2) cont = do
  c <- traceLet s o2 cont
  return $ CodeLet k o1 c
traceLet s (CodeCall reg name xds cont1) cont2 = do
  tmp <- traceLet s cont1 cont2
  return $ CodeCall reg name xds tmp
traceLet s (CodeLoad asm) cont = return $ CodeLet s asm cont

toLamSeq :: Comp -> WithEnv (Comp, [Identifier])
toLamSeq (Comp (_ :< CompLam x body)) = do
  (body', args) <- toLamSeq $ Comp body
  return (body', x : args)
toLamSeq t = return (t, [])

funAndArgsPol :: Comp -> WithEnv (Comp, [(Identifier, Value)])
funAndArgsPol (Comp (i :< CompApp e v)) = do
  (fun, xs) <- funAndArgsPol $ Comp e
  return (fun, (i, v) : xs)
funAndArgsPol c = return (c, [])

coFunAndArgsPol :: (Comp, [(Identifier, Value)]) -> Comp
coFunAndArgsPol (term, []) = term
coFunAndArgsPol (Comp term, (i, v):xs) =
  coFunAndArgsPol (Comp $ i :< CompApp term v, xs)
