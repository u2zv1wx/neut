module Modal
  ( modal
  ) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans.Except

import Data.List

import Data
import Reduce
import Util

import Control.Comonad.Cofree

import qualified Text.Show.Pretty as Pr

import Debug.Trace

modal :: WithEnv ()
modal = do
  penv <- gets polEnv
  forM_ penv $ \(name, e) -> do
    let (body, args) = toNegPiIntroSeq e
    body' <- modalNeg body
    insModalEnv name args body'

modalPos :: Pos -> WithEnv Value
modalPos (Pos (meta :< PosVar x)) = return $ Value $ meta :< ValueVar x
modalPos (Pos (meta :< PosConst x)) = return $ Value $ meta :< ValueConst x
modalPos (Pos (meta :< PosSigma xts t)) = do
  let (xs, ts) = unzip xts
  ts' <- mapM (modalPos . Pos) ts
  let ts'' = map (\(Value x) -> x) ts'
  Value t' <- modalPos $ Pos t
  return $ Value $ meta :< ValueSigma (zip xs ts'') t'
modalPos (Pos (meta :< PosSigmaIntro es)) = do
  ds <- mapM (modalPos . Pos) es
  let ds' = map (\(Value x) -> x) ds
  return $ Value $ meta :< ValueSigmaIntro ds'
modalPos (Pos (meta :< PosIndex l)) = return $ Value $ meta :< ValueIndex l
modalPos (Pos (meta :< PosIndexIntro l)) =
  return $ Value $ meta :< ValueIndexIntro l
modalPos (Pos (_ :< PosDown t)) = do
  t' <- modalNeg t
  closureType t'
modalPos (Pos (meta :< PosDownIntro abs)) = makeClosure meta abs
modalPos (Pos (meta :< PosUniv)) = return $ Value $ meta :< ValueUniv
modalPos (Pos (meta :< PosBox t)) = do
  t' <- modalNeg t
  return $ Value $ meta :< ValueBox t'
modalPos (Pos (meta :< PosBoxIntro e)) = do
  let (fun, args) = toNegPiIntroSeq e
  fun' <- modalNeg fun
  name <- newNameWith "box"
  insModalEnv name args fun'
  return $ Value $ meta :< ValueConst name

modalNeg :: Neg -> WithEnv Comp
modalNeg (Neg (meta :< NegPi (x, tdom) tcod)) = do
  tdom' <- modalPos tdom
  Comp tcod' <- modalNeg $ Neg tcod
  return $ Comp $ meta :< CompPi (x, tdom') tcod'
modalNeg lam@(Neg (meta :< NegPiIntro _ _)) = do
  let (body, args) = toNegPiIntroSeq lam
  xs <- takeNonBox $ varNeg lam
  body' <- modalNeg body
  lamName <- newNameWith "lam"
  insModalEnv lamName (xs ++ args) body'
  return $ Comp $ meta :< CompPiElim lamName (xs ++ args)
modalNeg app@(Neg (_ :< NegPiElim _ _)) = do
  let (fun, args) = toNegPiElimSeq app
  fun' <- modalNeg fun
  args' <- mapM modalPos args
  xs <- mapM (const (newNameWith "arg")) args
  app' <- tracePiElim fun' xs
  bindLet (zip xs args') app'
modalNeg (Neg (meta :< NegSigmaElim e1 xs e2)) = do
  e1' <- modalPos e1
  Comp e2' <- modalNeg $ Neg e2
  return $ Comp $ meta :< CompSigmaElim e1' xs e2'
modalNeg (Neg (meta :< NegIndexElim e branchList)) = do
  let (labelList, es) = unzip branchList
  es' <- mapM (modalNeg . Neg) es
  let es'' = map (\(Comp x) -> x) es'
  e' <- modalPos e
  return $ Comp $ meta :< CompIndexElim e' (zip labelList es'')
modalNeg (Neg (meta :< NegUpIntro v)) = do
  v' <- modalPos v
  return $ Comp $ meta :< CompUpIntro v'
modalNeg (Neg (meta :< NegUpElim x e1 e2)) = do
  Comp e1' <- modalNeg $ Neg e1
  Comp e2' <- modalNeg $ Neg e2
  return $ Comp $ meta :< CompUpElim x e1' e2'
modalNeg (Neg (meta :< NegDownElim e)) = callClosure meta e
modalNeg (Neg (meta :< NegBoxElim e)) = do
  e' <- modalPos e
  f <- newName
  bindLet [(f, e')] (Comp $ meta :< CompPiElim f [])

-- closureType t == Sigma (A : Ui). (Box (A -> t)) * A
closureType :: Comp -> WithEnv Value
closureType t = do
  (sigmaMeta, envInfo, piInfo, Value envType) <- closureType' t
  return $ Value $ sigmaMeta :< ValueSigma [envInfo, piInfo] envType

type IdentPlus = (Identifier, PreValue)

-- type IdentMinus = (Identifier, PreComp)
type ClsInfo = (Identifier, IdentPlus, IdentPlus, Value)

closureType' :: Comp -> WithEnv ClsInfo
closureType' (Comp t) = do
  envTypeName <- newNameWith "env"
  univMeta <- newNameWith "meta"
  -- insValueTypeEnv envTypeName $ Value $ univMeta :< ValueUniv
  envType <- toValueVar envTypeName
  piMeta <- newNameWith "meta"
  piArg <- newNameWith "arg"
  -- insValueTypeEnv piArg $ Value envType
  let piType = piMeta :< CompPi (piArg, envType) t
  boxMeta <- newNameWith "meta"
  let boxPiType = boxMeta :< ValueBox (Comp piType)
  sigmaMeta <- newNameWith "meta"
  let univ = univMeta :< ValueUniv
  sigmaArg <- newNameWith "arg"
  return (sigmaMeta, (envTypeName, univ), (sigmaArg, boxPiType), envType)

-- e ~> (env-type, name, env) : Sigma (A : Ui). (Box (Env -> N)) * Env
makeClosure :: Identifier -> Neg -> WithEnv Value
makeClosure meta abs = do
  let (Neg body, args) = toNegPiIntroSeq abs
  fvs <- takeNonBox $ nub $ varNeg abs
  placeHolder <- newNameWith "env"
  let envType = Value $ placeHolder :< ValueVar placeHolder
  envName <- newNameWith "env"
  body' <- makeClosureBody envName fvs body
  fun <- newNameWith "closure"
  insModalEnv fun (envName : args) body'
  funConst <- toValueConst fun
  envVar <- toValueVar envName -- fixme: use tensor
  let elems = map (\(Value x) -> x) [envType, funConst, envVar]
  return $ Value $ meta :< ValueSigmaIntro elems

-- Extract the values of free variables from the free-variable struct,
-- and then evaluate the original term.
makeClosureBody :: Identifier -> [Identifier] -> PreNeg -> WithEnv Comp
makeClosureBody _ [] funBody = modalNeg $ Neg funBody
makeClosureBody envName [x] funBody@(bodyMeta :< _) = do
  envMeta <- newNameWith "meta"
  upMeta <- newNameWith "meta"
  modalNeg $
    Neg $
    bodyMeta :<
    NegUpElim
      x
      (upMeta :< (NegUpIntro $ Pos $ envMeta :< PosVar envName))
      funBody
makeClosureBody envName xs funBody@(funMeta :< _) = do
  envMeta <- newNameWith "meta"
  modalNeg $
    Neg $ funMeta :< NegSigmaElim (Pos $ envMeta :< PosVar envName) xs funBody

callClosure :: Identifier -> Pos -> WithEnv Comp
callClosure meta e = do
  e' <- modalPos e
  envName <- newNameWith "env"
  fun <- newNameWith "fun"
  envTypeName <- newNameWith "type"
  return $
    Comp $
    meta :<
    CompSigmaElim
      e'
      [envTypeName, fun, envName]
      (meta :< CompPiElim fun [envName])

takeNonBox :: [Identifier] -> WithEnv [Identifier]
takeNonBox [] = return []
takeNonBox (x:xs) = do
  mt <- lookupTypeEnv x
  case mt of
    Nothing -> takeNonBox xs
    Just (_ :< NeutBox _) -> takeNonBox xs
    Just _ -> do
      xs' <- takeNonBox xs
      return $ x : xs'

bindLet :: [(Identifier, Value)] -> Comp -> WithEnv Comp
bindLet [] e = return e
bindLet ((x, v):rest) e@(Comp (compMeta :< _)) = do
  Comp e' <- bindLet rest e
  upMeta <- newNameWith "meta"
  return $ Comp $ compMeta :< CompUpElim x (upMeta :< CompUpIntro v) e'

tracePiElim :: Comp -> [Identifier] -> WithEnv Comp
tracePiElim (Comp (_ :< CompPi _ _)) _ =
  lift $ throwE "Modal.tracePiElim: type error"
tracePiElim (Comp (meta :< CompPiElim f xs)) args =
  return $ Comp $ meta :< CompPiElim f (xs ++ args)
tracePiElim (Comp (meta :< CompSigmaElim v xs e)) args = do
  Comp e' <- tracePiElim (Comp e) args
  return $ Comp $ meta :< CompSigmaElim v xs e'
tracePiElim (Comp (meta :< CompIndexElim v branchList)) args = do
  let (labelList, es) = unzip branchList
  es' <- mapM (\e -> tracePiElim (Comp e) args) es
  let es'' = map (\(Comp x) -> x) es'
  return $ Comp $ meta :< CompIndexElim v (zip labelList es'')
tracePiElim (Comp (_ :< CompUpIntro _)) _ =
  lift $ throwE "Modal.tracePiElim: type error"
tracePiElim (Comp (meta :< CompUpElim x e1 e2)) args = do
  Comp e2' <- tracePiElim (Comp e2) args
  return $ Comp $ meta :< CompUpElim x e1 e2'
