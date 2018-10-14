module Modal
  ( modalPos
  , modalNeg
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

modalPos :: Pos -> WithEnv Value
modalPos (Pos (meta :< PosVar x)) = do
  updateType x
  updateType meta
  return $ Value $ meta :< ValueVar x
modalPos (Pos (meta :< PosConst x)) = do
  updateType x
  updateType meta
  return $ Value $ meta :< ValueConst x
modalPos (Pos (meta :< PosPi (x, tdom) tcod)) = do
  Value tdom' <- modalPos $ Pos tdom
  Value tcod' <- modalPos $ Pos tcod
  return $ Value $ meta :< ValuePi (x, tdom') tcod'
modalPos (Pos (meta :< PosSigma xts t)) = do
  let (xs, ts) = unzip xts
  forM_ xs updateType
  ts' <- mapM (modalPos . Pos) ts
  let ts'' = map (\(Value x) -> x) ts'
  Value t' <- modalPos $ Pos t
  return $ Value $ meta :< ValueSigma (zip xs ts'') t'
modalPos (Pos (meta :< PosSigmaIntro es)) = do
  ds <- mapM (modalPos . Pos) es
  let ds' = map (\(Value x) -> x) ds
  updateType meta
  return $ Value $ meta :< ValueSigmaIntro ds'
modalPos (Pos (meta :< PosIndex l)) = return $ Value $ meta :< ValueIndex l
modalPos (Pos (meta :< PosIndexIntro l)) = do
  updateType meta
  updateLabelType l
  return $ Value $ meta :< ValueIndexIntro l
modalPos (Pos (meta :< PosUp t)) = do
  Value t' <- modalPos $ Pos t
  return $ Value $ meta :< ValueUp t'
modalPos (Pos (_ :< PosDown t)) = do
  Value t' <- modalPos $ Pos t
  closureType t'
modalPos (Pos (meta :< PosDownIntro abs)) = makeClosure meta abs
modalPos (Pos (meta :< PosUniv)) = return $ Value $ meta :< ValueUniv
modalPos (Pos (_ :< PosBox t)) = modalPos $ Pos t
modalPos (Pos (meta :< PosBoxIntro e)) = do
  let (fun, args) = toNegPiIntroSeq e
  fun' <- modalNeg fun
  name <- newNameWith "box"
  insModalEnv name args fun'
  updateType meta
  return $ Value $ meta :< ValueConst name

modalNeg :: Neg -> WithEnv Comp
modalNeg lam@(Neg (meta :< NegPiIntro _ _)) = do
  let (body@(Neg (bodyMeta :< _)), args) = toNegPiIntroSeq lam
  -- lambda-lifting for non-box variables
  xs <- takeNonBox $ varNeg lam
  body' <- modalNeg body
  lamName <- newNameWith "lam"
  -- set the type of lamName
  Value bodyType <- lookupPolTypeEnv' bodyMeta >>= modalPos . Pos
  lamType <- piSeqValueType (xs ++ args) bodyType
  insValueTypeEnv lamName $ Value lamType
  insModalEnv lamName (xs ++ args) body'
  -- return the lifted term
  updateType meta
  return $ Comp $ meta :< CompPiElim lamName (xs ++ args)
modalNeg app@(Neg (_ :< NegPiElim _ _)) = do
  let (fun, args) = toNegPiElimSeq app
  fun' <- modalNeg fun
  args' <- mapM modalPos args
  xs <- mapM (const (newNameWith "arg")) args
  ts <- mapM (\(Pos (meta :< _)) -> lookupPolTypeEnv' meta) args
  ts' <- mapM (modalPos . Pos) ts
  forM_ (zip xs ts') $ uncurry insValueTypeEnv
  app' <- tracePiElim fun' xs
  bindLet (zip xs args') app'
modalNeg (Neg (meta :< NegSigmaElim e1 xs e2)) = do
  e1' <- modalPos e1
  Comp e2' <- modalNeg $ Neg e2
  forM_ xs updateType
  updateType meta
  return $ Comp $ meta :< CompSigmaElim e1' xs e2'
modalNeg (Neg (meta :< NegIndexElim e branchList)) = do
  let (labelList, es) = unzip branchList
  es' <- mapM (modalNeg . Neg) es
  let es'' = map (\(Comp x) -> x) es'
  e' <- modalPos e
  updateType meta
  forM_ labelList updateLabelType
  return $ Comp $ meta :< CompIndexElim e' (zip labelList es'')
modalNeg (Neg (meta :< NegUpIntro v)) = do
  v' <- modalPos v
  updateType meta
  return $ Comp $ meta :< CompUpIntro v'
modalNeg (Neg (meta :< NegUpElim x e1 e2)) = do
  Comp e1' <- modalNeg $ Neg e1
  Comp e2' <- modalNeg $ Neg e2
  updateType meta
  return $ Comp $ meta :< CompUpElim x e1' e2'
modalNeg (Neg (meta :< NegDownElim e)) = callClosure meta e
modalNeg (Neg (meta :< NegBoxElim e)) = do
  e' <- modalPos e
  f <- newName
  updateType meta
  bindLet [(f, e')] (Comp $ meta :< CompPiElim f [])

-- closureType t == Sigma (A : Ui). (Box (A -> t)) * A
closureType :: PreValue -> WithEnv Value
closureType t = do
  (sigmaMeta, envInfo, piInfo, envType) <- closureType' t
  return $ Value $ sigmaMeta :< ValueSigma [envInfo, piInfo] envType

type IdentPlus = (Identifier, PreValue)

type ClsInfo = (Identifier, IdentPlus, IdentPlus, PreValue)

closureType' :: PreValue -> WithEnv ClsInfo
closureType' t = do
  envTypeName <- newNameWith "env"
  univMeta <- newNameWith "meta"
  insValueTypeEnv envTypeName $ Value $ univMeta :< ValueUniv
  Value envType <- toValueVar envTypeName
  piMeta <- newNameWith "meta"
  piArg <- newNameWith "arg"
  insValueTypeEnv piArg $ Value envType
  let piType = piMeta :< ValuePi (piArg, envType) t
  sigmaMeta <- newNameWith "meta"
  let univ = univMeta :< ValueUniv
  sigmaArg <- newNameWith "arg"
  return (sigmaMeta, (envTypeName, univ), (sigmaArg, piType), envType)

-- e ~> (env-type, name, env) : Sigma (A : Ui). (Box (Env -> N)) * Env
makeClosure :: Identifier -> Neg -> WithEnv Value
makeClosure meta abs@(Neg (absMeta :< _)) = do
  let (Neg body, args) = toNegPiIntroSeq abs
  -- construct the struct of free variables
  fvs <- takeNonBox $ nub $ varNeg abs
  ts <- mapM lookupPolTypeEnv' fvs
  envType <- tensorType ts >>= modalPos . Pos -- the type of the struct
  envName <- newNameWith "env"
  insValueTypeEnv envName envType
  -- construct the body of the closure-function
  body' <- makeClosureBody envName fvs body
  fun <- newNameWith "closure"
  insModalEnv fun (envName : args) body'
  vs <- mapM toValueVar [fun, envName]
  let elems = map (\(Value x) -> x) $ envType : vs
  -- represent (Down N) using sigma-type
  Value tAbs <- lookupPolTypeEnv' absMeta >>= modalPos . Pos
  tCls <- closureType tAbs
  insValueTypeEnv meta tCls
  return $ Value $ meta :< ValueSigmaIntro elems

-- Extract the values of free variables from the free-variable struct,
-- and then evaluate the original term.
makeClosureBody :: Identifier -> [Identifier] -> PreNeg -> WithEnv Comp
makeClosureBody _ [] funBody = modalNeg $ Neg funBody
makeClosureBody envName [x] funBody@(bodyMeta :< _) = do
  Value envType <- lookupValueTypeEnv' envName
  envMeta <- metaOfType $ Value envType
  upTypeMeta <- newNameWith "meta"
  let upType = upTypeMeta :< ValueUp envType
  upMeta <- metaOfType $ Value upType
  modalNeg $
    Neg $
    bodyMeta :<
    NegUpElim
      x
      (upMeta :< (NegUpIntro $ Pos $ envMeta :< PosVar envName))
      funBody
makeClosureBody envName xs funBody@(funMeta :< _) = do
  Value envType <- lookupValueTypeEnv' envName
  envMeta <- metaOfType $ Value envType
  modalNeg $
    Neg $ funMeta :< NegSigmaElim (Pos $ envMeta :< PosVar envName) xs funBody

metaOfType :: Value -> WithEnv Identifier
metaOfType t = do
  meta <- newNameWith "meta"
  insValueTypeEnv meta t
  return meta

callClosure :: Identifier -> Pos -> WithEnv Comp
callClosure meta e = do
  e' <- modalPos e
  Value t <- lookupValueTypeEnv' meta
  (_, (envTypeName, _), (_, piType), envType) <- closureType' t
  envName <- newNameWith "env"
  fun <- newNameWith "fun"
  insValueTypeEnv fun $ Value piType
  insValueTypeEnv envName $ Value envType
  updateType meta
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
  t <- lookupPolTypeEnv' x
  case t of
    _ :< PosBox _ -> takeNonBox xs
    _ -> do
      xs' <- takeNonBox xs
      return $ x : xs'

bindLet :: [(Identifier, Value)] -> Comp -> WithEnv Comp
bindLet [] e = return e
bindLet ((x, v@(Value (valueMeta :< _))):rest) e@(Comp (compMeta :< _)) = do
  Comp e' <- bindLet rest e
  Value valueType <- lookupValueTypeEnv' valueMeta
  insValueTypeEnv x $ Value valueType
  upTypeMeta <- newNameWith "meta"
  let upType = upTypeMeta :< ValueUp valueType
  upMeta <- newNameWith "meta"
  insValueTypeEnv upMeta $ Value upType
  return $ Comp $ compMeta :< CompUpElim x (upMeta :< CompUpIntro v) e'

tracePiElim :: Comp -> [Identifier] -> WithEnv Comp
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

updateType :: Identifier -> WithEnv ()
updateType x = lookupPolTypeEnv' x >>= modalPos . Pos >>= insValueTypeEnv x

updateLabelType :: Index -> WithEnv ()
updateLabelType (IndexLabel x) = updateType x
updateLabelType _ = return ()
