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
virtualV (Value (_ :< ValueVar x)) = return $ DataPointer x
virtualV (Value (i :< ValueThunk comp@(Comp (compMeta :< _)))) = do
  asm <- virtualC comp
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
  insCodeEnv label [envName] asm
  return $ DataClosure label envName fvList

virtualC :: Comp -> WithEnv Code
virtualC lam@(Comp (i :< CompLam _ _)) = do
  (body, args) <- toLamSeq lam
  bodyCode <- virtualC body
  name <- newNameWith "lam"
  lamType <- lookupTypeEnv' i
  insTypeEnv name lamType
  insCodeEnv name args bodyCode
  return $ CodeReturn $ DataLabel name
virtualC app@(Comp (i :< CompApp _ _)) = do
  (fun@(Comp (funMeta :< _)), ivs) <- funAndArgsPol app
  let (_, vs) = unzip ivs
  ds <- mapM virtualV vs
  fun' <- virtualC fun
  funName <- newNameWith "fun"
  funType <- lookupTypeEnv' funMeta
  insTypeEnv funName funType
  s <- newNameWith "tmp"
  resultType <- lookupTypeEnv' i
  insTypeEnv s resultType
  traceLet funName fun' $ CodeCall s funName ds (CodeReturn (DataPointer s))
virtualC (Comp (_ :< CompLift v)) = do
  ans <- virtualV v
  return $ CodeReturn ans
virtualC (Comp (_ :< CompBind s comp1 comp2)) = do
  operation1 <- virtualC (Comp comp1)
  operation2 <- virtualC (Comp comp2)
  traceLet s operation1 operation2
virtualC (Comp (i :< CompUnthunk v)) = do
  asm <- virtualV v
  s <- newNameWith "tmp"
  resultType <- lookupTypeEnv' i
  insTypeEnv s resultType
  return $ CodeCallClosure s asm (CodeReturn (DataPointer s))
virtualC (Comp (_ :< CompMu s comp)) = do
  asm <- virtualC $ Comp comp
  undefined
  -- undefined -- insCodeEnv s s asm'
  -- -- return $ CodeRecursiveJump
virtualC (Comp (_ :< CompDecision vs tree)) = do
  valueList <-
    forM vs $ \v -> do
      asm <- virtualV v
      i <- newNameWith "seq"
      return (i, asm)
  let (is, asms) = unzip valueList
  body <- virtualDecision is tree
  letSeq is asms body

virtualDecision :: [Identifier] -> Decision PreComp -> WithEnv Code
virtualDecision asmList (DecisionLeaf ois e) = do
  let varList = map snd ois
  asmList' <-
    forM (zip asmList ois) $ \(x, (index, _)) ->
      return $ DataElemAtIndex x index
  body <- virtualC $ Comp e
  letSeq varList asmList' body
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
  -> Index
  -> [(Identifier, Int, Identifier, Code)]
  -> Maybe (Maybe Identifier, Identifier, Code)
  -> WithEnv Code
makeBranch _ _ [] Nothing = error "empty branch"
makeBranch y o js@((_, _, target, code):_) Nothing =
  if null o
    then return (CodeSwitch y (target, code) js)
    else do
      let tmp = DataElemAtIndex y o
      name <- newName
      let tmp2 = CodeSwitch name (target, code) js
      return $ CodeLet name tmp tmp2
makeBranch y o js (Just (Just defaultName, label, code)) =
  if null o
    then return (CodeSwitch y (label, code) js)
    else do
      let tmp = CodeSwitch defaultName (label, code) js
      return $ CodeLet defaultName (DataElemAtIndex y o) tmp
makeBranch y o js (Just (Nothing, label, code)) =
  if null o
    then return (CodeSwitch y (label, code) js)
    else do
      let tmp = DataElemAtIndex y o
      name <- newName
      let tmp2 = CodeSwitch name (label, code) js
      return $ CodeLet name tmp tmp2

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
  undefined
  let (_, ds) = unzip cds
  let vs = join $ map varDecision ds
  case mdefault of
    Nothing                -> vs
    Just (Nothing, tree)   -> vs ++ varDecision tree
    Just (Just name, tree) -> vs ++ filter (/= name) (varDecision tree)
varDecision (DecisionSwap _ tree) = varDecision tree
