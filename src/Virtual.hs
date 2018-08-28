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
virtualV (Value (i :< ValueVar x)) = return $ i :< DataPointer x
virtualV (Value (i :< ValueConst x)) = do
  t <- lookupTypeEnv' i
  case t of
    Fix (TypeDown _) -> do
      envName <- newNameWith "fv"
      let envType = Fix (TypeDown (Fix (TypeStruct [])))
      insTypeEnv envName envType
      return $ i :< DataClosure x envName []
    _ -> return $ i :< DataFunName x
virtualV (Value (i :< ValueThunk comp@(Comp (compMeta :< _)))) = do
  let fvList = varN comp
  fvTypeList <- mapM lookupTypeEnv' fvList
  envName <- newNameWith "fv"
  -- envName : &{posType-1, ..., posType-n}
  let envType = Fix (TypeDown (Fix (TypeStruct fvTypeList)))
  insTypeEnv envName envType
  let label = "thunk" ++ i
  compType <- lookupTypeEnv' compMeta
  -- thunk : &(&type-of-env -> type-of-comp)
  let labelType = Fix (TypeDown (Fix (TypeForall (envName, envType) compType)))
  insTypeEnv label labelType
  asm <- virtualC comp
  insCodeEnv label [envName] asm
  return $ i :< DataClosure label envName fvList

virtualC :: Comp -> WithEnv Code
virtualC lam@(Comp (_ :< CompLam _ _)) = do
  (body, args) <- toLamSeq lam
  bodyCode <- virtualC body
  name <- newNameWith "lam"
  let labelPointerType = Fix $ TypeDown $ Fix $ TypeInt 8
  -- name : &(P -> N) (must be a pointer)
  -- ~> name : &i8 (just a reference)
  insTypeEnv name labelPointerType
  insCodeEnv name args bodyCode
  meta <- newNameWith "meta"
  insTypeEnv meta labelPointerType
  return $ CodeReturn $ meta :< DataFunName name
virtualC app@(Comp (i :< CompApp _ _)) = do
  (fun@(Comp (funMeta :< _)), ivs) <- funAndArgsPol app
  let (_, vs) = unzip ivs
  ds <- mapM virtualV vs
  funCode <- virtualC fun
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
  traceLet funName funCode $
    CodeCall s funName ds (CodeReturn (meta :< DataPointer s))
virtualC (Comp (_ :< CompLift v)) = do
  ans <- virtualV v
  return $ CodeReturn ans
virtualC (Comp (_ :< CompBind s comp1 comp2)) = do
  operation1 <- virtualC (Comp comp1)
  operation2 <- virtualC (Comp comp2)
  traceLet s operation1 operation2
virtualC (Comp (i :< CompUnthunk v@(Value (valueMeta :< _)))) = do
  asm <- virtualV v
  s <- newNameWith "tmp"
  resultType <- lookupTypeEnv' i
  insTypeEnv s resultType
  return $ CodeCallClosure s asm (CodeReturn (valueMeta :< DataPointer s))
virtualC (Comp (_ :< CompMu s comp)) = do
  asm <- virtualC $ Comp comp
  insCodeEnv s [] asm
  meta <- newNameWith "meta"
  let labelPointerType = Fix $ TypeDown $ Fix $ TypeInt 8
  insTypeEnv meta labelPointerType
  return $ CodeReturn $ meta :< DataFunName s
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
traceLet s (CodeReturn ans) cont = return $ CodeLet s ans cont
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
traceLet s (CodeCallClosure reg env cont1) cont2 = do
  tmp <- traceLet s cont1 cont2
  return $ CodeCallClosure reg env tmp

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

varP :: Value -> [Identifier]
varP (Value (_ :< ValueVar s))   = [s]
varP (Value (_ :< ValueConst _)) = []
varP (Value (_ :< ValueThunk e)) = varN e

varN :: Comp -> [Identifier]
varN (Comp (_ :< CompLam s e)) = filter (/= s) $ varN (Comp e)
varN (Comp (_ :< CompApp e v)) = varN (Comp e) ++ varP v
varN (Comp (_ :< CompLift v)) = varP v
varN (Comp (_ :< CompBind s e1 e2)) =
  varN (Comp e1) ++ filter (/= s) (varN (Comp e2))
varN (Comp (_ :< CompUnthunk v)) = varP v
varN (Comp (_ :< CompMu s e)) = filter (/= s) $ varN (Comp e)
varN (Comp (_ :< CompDecision vs tree)) = do
  let vs1 = join $ map varP vs
  let vs2 = varDecision tree
  vs1 ++ vs2

varDecision :: Decision PreComp -> [Identifier]
varDecision (DecisionLeaf ois e) = do
  let bounds = map snd ois
  filter (`notElem` bounds) $ varN $ Comp e
varDecision (DecisionSwitch _ cds mdefault) = do
  let (_, ds) = unzip cds
  let vs = join $ map varDecision ds
  case mdefault of
    Nothing                -> vs
    Just (Nothing, tree)   -> vs ++ varDecision tree
    Just (Just name, tree) -> vs ++ filter (/= name) (varDecision tree)
varDecision (DecisionSwap _ tree) = varDecision tree
