module Virtual
  ( virtualPos
  , virtualNeg
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

virtualPos :: Pos -> WithEnv Data
virtualPos (Pos (_ :< PosVar x)) = return (DataLocal x)
virtualPos (Pos (_ :< PosConst x)) = return $ DataLabel x
virtualPos (Pos (_ :< PosPi _ _)) = return $ DataInt32 0
virtualPos (Pos (_ :< PosSigma _ _)) = return $ DataInt32 0
virtualPos (Pos (_ :< PosSigmaIntro es)) = do
  ds <- mapM (virtualPos . Pos) es
  return $ DataStruct ds
virtualPos (Pos (_ :< PosIndex _)) = return $ DataInt32 0
virtualPos (Pos (_ :< PosIndexIntro x)) = do
  i <- indexToInt x
  return $ DataInt32 i
virtualPos (Pos (_ :< PosUp _)) = return $ DataInt32 0
virtualPos (Pos (_ :< PosDown _)) = return $ DataInt32 0
virtualPos (Pos (_ :< PosDownIntro abs)) = do
  let (Neg funBody@(funMeta :< _), args) = toNegPiIntroSeq abs
  let fvs = nub $ varNeg abs
  ts <- mapM lookupPolTypeEnv' fvs
  envType <- tensorType ts
  tfun <- lookupPolTypeEnv' funMeta
  cls <- newNameWith "closure"
  tmp <- newNameWith "meta"
  boxTmp <- newNameWith "meta"
  envName <- newNameWith "env"
  insPolTypeEnv cls $ boxTmp :< PosBox (tmp :< PosPi (envName, envType) tfun)
  funBody' <-
    case fvs of
      [] -> do
        tmp <- newNameWith "meta"
        insPolTypeEnv envName $ tmp :< PosIndex "top"
        virtualNeg $ Neg funBody
      [x] -> do
        tmp <- newNameWith "meta"
        let piType = tmp :< PosPi (x, envType) tfun
        piMeta <- newNameWith "meta"
        insPolTypeEnv piMeta piType
        envMeta <- newNameWith "meta"
        insPolTypeEnv envMeta envType
        insPolTypeEnv envName envType
        virtualNeg $
          Neg $
          funMeta :<
          NegPiElim
            (piMeta :< NegPiIntro x funBody)
            (Pos $ envMeta :< PosVar envName)
      _ -> do
        envMeta <- newNameWith "meta"
        insPolTypeEnv envMeta envType
        insPolTypeEnv envName envType
        virtualNeg $
          Neg $
          funMeta :< NegSigmaElim (Pos $ envMeta :< PosVar envName) fvs funBody
  insCodeEnv cls (envName : args) funBody'
  return $ DataClosure cls envName fvs
virtualPos (Pos (_ :< PosUniv)) = return $ DataInt32 0
virtualPos (Pos (_ :< PosBox _)) = return $ DataInt32 0
virtualPos (Pos (meta :< PosBoxIntro e)) = do
  let (fun, args) = toNegPiIntroSeq e
  fun' <- virtualNeg fun
  name <- newNameWith "box"
  boxType <- lookupPolTypeEnv' meta
  insPolTypeEnv name boxType
  insCodeEnv name args fun'
  return $ DataLabel name

virtualNeg :: Neg -> WithEnv Code
virtualNeg lam@(Neg (_ :< NegPiIntro _ _)) = do
  let (body@(Neg (bodyMeta :< _)), args) = toNegPiIntroSeq lam
  lamName <- newNameWith "lam"
  body' <- virtualNeg body
  insCodeEnv lamName args body'
  bodyType <- lookupPolTypeEnv' bodyMeta
  lamType <- piSeqType args bodyType
  tmp <- newName
  let boxLamType = tmp :< PosBox lamType
  insPolTypeEnv lamName boxLamType
  return $ CodeBoxElim $ DataLabel lamName
virtualNeg app@(Neg (_ :< NegPiElim _ _)) = do
  let (fun, args) = toNegPiElimSeq app
  dataList <- mapM virtualPos args
  ts <- mapM (\(Pos (meta :< _)) -> lookupPolTypeEnv' meta) args
  xs <- mapM (const newName) dataList
  forM_ (zip xs ts) $ uncurry insPolTypeEnv
  (funName, fvs) <- boxify fun
  return $ bindLet (zip xs dataList) $ CodeCallTail funName (fvs ++ xs)
virtualNeg (Neg (_ :< NegSigmaElim e1@(Pos (meta1 :< _)) xs e2)) = do
  e1' <- virtualPos e1
  e2' <- virtualNeg $ Neg e2
  z <- newName
  sigmaType <- lookupPolTypeEnv' meta1
  insPolTypeEnv z sigmaType
  return $ CodeLet z e1' $ extract z (zip xs [0 ..]) e2'
virtualNeg (Neg (_ :< NegIndexElim e@(Pos (meta :< _)) branchList)) = do
  let (labelList, es) = unzip branchList
  es' <- mapM (virtualNeg . Neg) es
  e' <- virtualPos e
  z <- newName
  t <- lookupPolTypeEnv' meta
  insPolTypeEnv z t
  return $ CodeLet z e' $ CodeSwitch z $ zip labelList es'
virtualNeg (Neg (_ :< NegUpIntro v)) = do
  d <- virtualPos v
  return $ CodeReturn d
virtualNeg (Neg (_ :< NegUpElim x e1 e2)) = do
  e1' <- virtualNeg $ Neg e1
  e2' <- virtualNeg $ Neg e2
  return $ traceLet x e1' e2'
virtualNeg (Neg (_ :< NegDownElim e)) = do
  e' <- virtualPos e
  envName <- newNameWith "env"
  envType <- opaque
  insPolTypeEnv envName envType
  fun <- newNameWith "fun"
  funType <- opaquePi >>= withBox
  insPolTypeEnv fun funType
  cls <- newNameWith "cls"
  clsType <- toSigma funType envType
  insPolTypeEnv cls clsType
  return $
    CodeLet cls e' $
    extract cls [(fun, 0), (envName, 1)] $ CodeCallTailCls fun envName
virtualNeg (Neg (_ :< NegBoxElim e)) = do
  e' <- virtualPos e
  return $ CodeBoxElim e'

extract :: Identifier -> [(Identifier, Int)] -> Code -> Code
extract z [] cont = CodeFree z cont
extract z ((x, i):xis) cont = do
  let cont' = extract z xis cont
  CodeExtractValue x z i cont'

bindLet :: [(Identifier, Data)] -> Code -> Code
bindLet [] e = e
bindLet ((x, d):xds) e = CodeLet x d $ bindLet xds e

traceLet :: String -> Code -> Code -> Code
traceLet s (CodeReturn ans) cont = CodeLet s ans cont
traceLet s (CodeLet k o1 o2) cont = CodeLet k o1 $ traceLet s o2 cont
traceLet s (CodeCall reg name xds cont1) cont2 =
  CodeCall reg name xds $ traceLet s cont1 cont2
traceLet s (CodeCallTail name xds) cont = CodeCall s name xds cont
traceLet s (CodeCallTailCls name envName) cont =
  CodeCall s name [envName] $ CodeFree envName cont
traceLet x (CodeSwitch y branchList) cont = do
  let (labelList, es) = unzip branchList
  let es' = map (\e -> traceLet x e cont) es
  CodeSwitch y $ zip labelList es'
traceLet s (CodeExtractValue x basePointer i cont1) cont2 =
  CodeExtractValue x basePointer i $ traceLet s cont1 cont2
traceLet s (CodeFree x cont1) cont2 = CodeFree x $ traceLet s cont1 cont2
traceLet s (CodeBoxElim d) cont = CodeLet s d cont

boxify :: Neg -> WithEnv (Identifier, [Identifier])
boxify abs = do
  let (fun@(Neg (meta :< _)), args) = toNegPiIntroSeq abs
  let fvs = nub $ varNeg abs
  tfun <- lookupPolTypeEnv' meta
  lamType <- piSeqType fvs tfun
  tmp <- newNameWith "meta"
  let boxLamType = tmp :< PosBox lamType
  boxLamName <- newNameWith "lam.box"
  insPolTypeEnv boxLamName boxLamType
  fun' <- virtualNeg fun
  insCodeEnv boxLamName (fvs ++ args) fun'
  return (boxLamName, fvs)

opaque :: WithEnv PrePos
opaque = do
  meta <- newNameWith "meta"
  return $ meta :< PosIndex "opaque"

opaquePi :: WithEnv PrePos
opaquePi = do
  o1 <- opaque
  o2 <- opaque
  upMeta <- newNameWith "meta"
  x <- newNameWith "arg"
  insPolTypeEnv x o1
  piMeta <- newNameWith "meta"
  return $ piMeta :< PosPi (x, o1) (upMeta :< PosUp o2)

withBox :: PrePos -> WithEnv PrePos
withBox t = do
  boxMeta <- newNameWith "meta"
  return $ boxMeta :< PosBox t

toSigma :: PrePos -> PrePos -> WithEnv PrePos
toSigma t1 t2 = do
  x <- newName
  insPolTypeEnv x t1
  meta <- newNameWith "meta"
  return $ meta :< PosSigma [(x, t1)] t2
