module Modal
  ( modalize
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

modalize :: WithEnv ()
modalize = do
  penv <- gets polEnv
  forM_ penv $ \(name, e) -> do
    e' <- modalNeg e
    insModalEnv name [] e'

modalPos :: Pos -> WithEnv Value
modalPos (PosVar x) = return $ ValueVar x
modalPos (PosSigma xts t) = do
  let (xs, ts) = unzip xts
  ts' <- mapM modalPos ts
  t' <- modalPos t
  return $ ValueSigma (zip xs ts') t'
modalPos (PosSigmaIntro es) = do
  ds <- mapM modalPos es
  return $ ValueSigmaIntro ds
modalPos (PosIndex l) = return $ ValueIndex l
modalPos (PosIndexIntro l meta) = return $ ValueIndexIntro l meta
modalPos (PosDown t) = do
  t' <- modalNeg t
  closureType t'
modalPos (PosDownIntro e) = makeClosure e
modalPos PosUniv = return ValueUniv
modalPos (PosBox t) = do
  t' <- modalNeg t
  return $ ValueBox t'
modalPos (PosBoxIntro e) = makeClosure e
modalPos (PosConst t) = do
  t' <- modalPos t
  return $ ValueConst t'
modalPos (PosConstIntro x) = return $ ValueConstIntro x
modalPos (PosArith kind e1 e2) = do
  e1' <- modalPos e1
  e2' <- modalPos e2
  return $ ValueArith kind e1' e2'

modalNeg :: Neg -> WithEnv Comp
modalNeg (NegPi (x, tdom) tcod) = do
  tdom' <- modalPos tdom
  tcod' <- modalNeg tcod
  return $ CompPi (x, tdom') tcod'
modalNeg lam@(NegPiIntro _ _) = do
  let (body, args) = toNegPiIntroSeq lam
  let xs = varNeg lam
  body' <- modalNeg body
  lamName <- newNameWith "lam"
  insModalEnv lamName (xs ++ args) body'
  return $ CompPiElimConstElim lamName (xs ++ args)
modalNeg app@(NegPiElim _ _) = do
  let (fun, args) = toNegPiElimSeq app
  fun' <- modalNeg fun
  args' <- mapM modalPos args
  xs <- mapM (const (newNameWith "arg")) args
  app' <- commPiElim fun' xs
  bindLet (zip xs args') app'
modalNeg (NegSigmaElim e1 xs e2) = do
  e1' <- modalPos e1
  e2' <- modalNeg e2
  return $ CompSigmaElim e1' xs e2'
modalNeg (NegIndexElim e branchList) = do
  let (labelList, es) = unzip branchList
  es' <- mapM modalNeg es
  e' <- modalPos e
  return $ CompIndexElim e' (zip labelList es')
modalNeg (NegUpIntro v) = do
  v' <- modalPos v
  return $ CompUpIntro v'
modalNeg (NegUpElim x e1 e2) = do
  e1' <- modalNeg e1
  e2' <- modalNeg e2
  return $ CompUpElim x e1' e2'
modalNeg (NegDownElim e) = callClosure e
modalNeg (NegBoxElim e) = callClosure e
modalNeg (NegConstElim e) = do
  e' <- modalPos e
  x <- newNameWith "const"
  bindLet [(x, e')] $ CompPiElimConstElim x []
modalNeg (NegMu self e) = do
  let (body, args) = toNegPiIntroSeq e
  let xs = varNeg $ NegMu self e
  body' <- modalNeg body
  insModalEnv self (xs ++ args) body'
  return $ CompPiElimConstElim self (xs ++ args)
modalNeg (NegPrint t e) = do
  e' <- modalPos e
  return $ CompPrint t e'

-- closureType t == Sigma (A : Ui). (Box (A -> t)) * A
closureType :: Comp -> WithEnv Value
closureType t = do
  (envInfo, piInfo, envType) <- closureType' t
  return $ ValueSigma [envInfo, piInfo] envType

type IdentPlus = (Identifier, Value)

type ClsInfo = (IdentPlus, IdentPlus, Value)

closureType' :: Comp -> WithEnv ClsInfo
closureType' t = do
  envTypeName <- newNameWith "env"
  piArg <- newNameWith "arg"
  let piType = CompPi (piArg, ValueVar envTypeName) t
  let boxPiType = ValueBox piType
  let univ = ValueUniv
  sigmaArg <- newNameWith "arg"
  return ((envTypeName, univ), (sigmaArg, boxPiType), ValueVar envTypeName)

-- e ~> (env-type, name, env) : Sigma (A : Ui). (Box (Env -> N)) * Env
makeClosure :: Neg -> WithEnv Value
makeClosure abs = do
  let (body, args) = toNegPiIntroSeq abs
  let fvs = nub $ varNeg abs
  envName <- newNameWith "env"
  body' <- makeClosureBody envName fvs body
  cls <- newNameWith "closure"
  insModalEnv cls (envName : args) body'
  let vs = map ValueVar fvs
  return $ ValueSigmaIntro [ValueConstIntro cls, ValueSigmaIntro vs]

-- Extract the values of free variables from the free-variable struct,
-- and then evaluate the original term.
makeClosureBody :: Identifier -> [Identifier] -> Neg -> WithEnv Comp
makeClosureBody _ [] funBody = modalNeg funBody
makeClosureBody envName [x] funBody =
  modalNeg $ NegUpElim x (NegUpIntro $ PosVar envName) funBody
makeClosureBody envName xs funBody =
  modalNeg $ NegSigmaElim (PosVar envName) xs funBody

callClosure :: Pos -> WithEnv Comp
callClosure e = do
  e' <- modalPos e
  envName <- newNameWith "env"
  fun <- newNameWith "fun"
  return $ CompSigmaElim e' [fun, envName] (CompPiElimConstElim fun [envName])

bindLet :: [(Identifier, Value)] -> Comp -> WithEnv Comp
bindLet [] e = return e
bindLet ((x, v):rest) e = do
  e' <- bindLet rest e
  return $ CompUpElim x (CompUpIntro v) e'

-- commutative conversion for pi-elimination
commPiElim :: Comp -> [Identifier] -> WithEnv Comp
commPiElim (CompPi _ _) _ = lift $ throwE "Modal.commPiElim: type error"
commPiElim (CompPiElimConstElim f xs) args =
  return $ CompPiElimConstElim f (xs ++ args)
commPiElim (CompSigmaElim v xs e) args = do
  e' <- commPiElim e args
  return $ CompSigmaElim v xs e'
commPiElim (CompIndexElim v branchList) args = do
  let (labelList, es) = unzip branchList
  es' <- mapM (`commPiElim` args) es
  return $ CompIndexElim v (zip labelList es')
commPiElim (CompUpIntro _) _ = lift $ throwE "Modal.commPiElim: type error"
commPiElim (CompUpElim x e1 e2) args = do
  e2' <- commPiElim e2 args
  return $ CompUpElim x e1 e2'
commPiElim CompPrint {} _ = lift $ throwE "Modal.commPiElim: type error"
