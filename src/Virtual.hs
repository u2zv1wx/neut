module Virtual
  ( virtualPos
  , virtualNeg
  ) where

import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Data.List

import           Data
import           Reduce
import           Util

import           Control.Comonad.Cofree

import qualified Text.Show.Pretty           as Pr

import           Debug.Trace

virtualPos :: Pos -> WithEnv Data
virtualPos (PosVar x) = return (DataLocal x)
virtualPos (PosConst x) = return $ DataLabel x
virtualPos (PosPi _ _) = return $ DataInt32 0
virtualPos (PosSigma _ _) = return $ DataInt32 0
virtualPos (PosSigmaIntro es) = do
  ds <- mapM virtualPos es
  return $ DataStruct ds
virtualPos (PosIndex _) = return $ DataInt32 0
virtualPos (PosIndexIntro x) = do
  i <- indexToInt x
  return $ DataInt32 i
virtualPos (PosUp _) = return $ DataInt32 0
virtualPos (PosDown _) = return $ DataInt32 0
virtualPos (PosDownIntro e) = do
  envName <- newNameWith "env"
  let fvs = nub $ varNeg e
  e' <- virtualNeg $ NegSigmaElim (PosVar envName) fvs e
  cls <- newNameWith "closure"
  insCodeEnv cls [envName] e'
  return $ DataClosure cls envName fvs
virtualPos PosUniv = return $ DataInt32 0
virtualPos (PosBox _) = return $ DataInt32 0

virtualNeg :: Neg -> WithEnv Code
virtualNeg lam@(NegPiIntro _ _) = do
  let (body, args) = toNegPiIntroSeq lam
  name <- newNameWith "lam"
  body' <- virtualNeg body
  insCodeEnv name args body'
  return $ CodeReturn (DataLabel name)
virtualNeg app@(NegPiElim _ _) = do
  let (fun, args) = toNegPiElimSeq app
  dataList <- mapM virtualPos args
  funCode <- virtualNeg fun
  funName <- newNameWith "fun"
  s <- newName
  xs <- mapM (const newName) dataList
  return $
    bindLet (zip xs dataList) $
    traceLet funName funCode $ CodeCall s funName xs (CodeReturn (DataLocal s))
virtualNeg (NegSigmaElim e1 xs e2) = do
  e1' <- virtualPos e1
  e2' <- virtualNeg e2
  z <- newName
  ts <- mapM (lookupTypeEnv' >=> reduce >=> toLowType) xs
  return $ CodeLet z e1' $ extract z ts (zip xs [0 ..]) e2'
virtualNeg (NegIndexElim e branchList) = do
  let (labelList, es) = unzip branchList
  es' <- mapM virtualNeg es
  e' <- virtualPos e
  z <- newName
  return $ CodeLet z e' $ CodeSwitch z $ zip labelList es'
virtualNeg (NegUpIntro v) = do
  d <- virtualPos v
  return $ CodeReturn d
virtualNeg (NegUpElim x e1 e2) = do
  e1' <- virtualNeg e1
  e2' <- virtualNeg e2
  return $ traceLet x e1' e2'
virtualNeg (NegDownElim e) = do
  e' <- virtualPos e
  fun <- newNameWith "fun"
  envName <- newNameWith "env"
  cls <- newNameWith "cls"
  s <- newNameWith "tmp"
  let ts = [LowTypePointer (LowTypeInt 32), LowTypePointer (LowTypeInt 32)]
  return $
    CodeLet cls e' $
    extract cls ts [(fun, 0), (envName, 1)] $
    CodeCall s fun [envName] $ CodeFree envName $ CodeReturn (DataLocal s)
virtualNeg (NegBoxIntro e) = do
  e' <- virtualNeg e
  name <- newNameWith "box"
  insCodeEnv name [] e'
  return $ CodeReturn (DataLabel name)
virtualNeg (NegBoxElim e) = do
  e' <- virtualNeg e
  funName <- newNameWith "unbox"
  s <- newName
  return $
    traceLet funName e' $ CodeCall s funName [] (CodeReturn (DataLocal s))

extract :: Identifier -> [LowType] -> [(Identifier, Int)] -> Code -> Code
extract z _ [] cont = CodeFree z cont
extract z ts ((x, i):xis) cont = do
  let cont' = extract z ts xis cont
  CodeExtractValue x (z, ts) i cont'

bindLet :: [(Identifier, Data)] -> Code -> Code
bindLet [] e           = e
bindLet ((x, d):xds) e = CodeLet x d $ bindLet xds e

traceLet :: String -> Code -> Code -> Code
traceLet s (CodeReturn ans) cont = CodeLet s ans cont
traceLet s (CodeLet k o1 o2) cont = do
  let c = traceLet s o2 cont
  CodeLet k o1 c
traceLet s (CodeCall reg name xds cont1) cont2 = do
  let tmp = traceLet s cont1 cont2
  CodeCall reg name xds tmp
traceLet x (CodeSwitch y branchList) cont = do
  let (labelList, es) = unzip branchList
  let es' = map (\e -> traceLet x e cont) es
  CodeSwitch y $ zip labelList es'
traceLet s (CodeExtractValue x (basePointer, ts) i cont1) cont2 = do
  let tmp = traceLet s cont1 cont2
  CodeExtractValue x (basePointer, ts) i tmp
traceLet s (CodeFree x cont1) cont2 = do
  let tmp = traceLet s cont1 cont2
  CodeFree x tmp
-- freeAtTail :: String -> Code -> Code
-- freeAtTail s (CodeReturn ans) = CodeFree s (CodeReturn ans)
-- freeAtTail s (CodeLet k o1 o2) = CodeLet k o1 (freeAtTail s o2)
-- freeAtTail s (CodeCall reg name xds cont) =
--   CodeCall reg name xds (freeAtTail s cont)
-- freeAtTail x (CodeSwitch y branchList) = do
--   let (labelList, es) = unzip branchList
--   let es' = map (freeAtTail x) es
--   CodeSwitch y $ zip labelList es'
-- freeAtTail s (CodeExtractValue x (basePointer, ts) i cont) =
--   CodeExtractValue x (basePointer, ts) i (freeAtTail s cont)
-- freeAtTail s (CodeFree x cont) = CodeFree x (freeAtTail s cont)
