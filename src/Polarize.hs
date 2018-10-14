module Polarize
  ( polarizeNeg
  , polarize
  ) where

import Control.Monad

import Control.Comonad.Cofree

import Control.Monad.State
import Control.Monad.Trans.Except

import qualified Text.Show.Pretty as Pr

import Data
import Util

import Data.Maybe (maybeToList)

polarize :: [(Identifier, Neut)] -> Neut -> WithEnv Neg
polarize [] final = polarizeNeg final
polarize ((x, e):rest) final = do
  lookupTypeEnv' x >>= polarizePos >>= \(Pos t) -> insPolTypeEnv x t
  Neg cont@(codMeta :< _) <- polarize rest final
  Neg e' <- polarizeNeg e
  codType <- lookupPolTypeEnv' codMeta
  meta <- newNameWith "meta"
  insPolTypeEnv meta codType
  return $ Neg $ meta :< NegUpElim x e' cont

polarizeNeg :: Neut -> WithEnv Neg
polarizeNeg e@(_ :< NeutVar _) = posRet e
polarizeNeg e@(_ :< NeutConst _ _) = posRet e
polarizeNeg pi@(_ :< NeutPi _ _) = posRet pi
polarizeNeg lam@(_ :< NeutPiIntro _ _) = posRet lam
polarizeNeg (meta :< NeutPiElim e1@(meta1 :< _) e2@(meta2 :< _)) = do
  (_, retMeta) <- lookupTypeEnv' meta >>= polarizePos >>= toRetType'
  f <- newNameWith "pi"
  v <- newNameWith "arg"
  Pos t1 <- lookupTypeEnv' meta1 >>= polarizePos
  Pos t2 <- lookupTypeEnv' meta2 >>= polarizePos
  case t1 of
    _ :< PosDown tfun -> do
      insPolTypeEnv meta1 t1
      insPolTypeEnv meta2 t2
      funMeta <- newNameWith "meta"
      insPolTypeEnv funMeta tfun
      bindSeq
        [(v, e2), (f, e1)]
        (Neg $
         retMeta :<
         NegPiElim
           (funMeta :< NegDownElim (Pos $ meta1 :< PosVar f))
           (Pos $ meta2 :< PosVar v))
    _ -> lift $ throwE "Polarize.polarize: type error"
polarizeNeg e@(_ :< NeutSigma _ _) = posRet e
polarizeNeg (meta :< NeutSigmaIntro es) = do
  nameList <- mapM (const newName) es
  nameList' <- mapM toPosVar nameList
  (_, retMeta) <- lookupTypeEnv' meta >>= polarizePos >>= toRetType'
  Pos tSigma <- lookupTypeEnv' meta >>= polarizePos
  sigmaMeta <- newNameWith "meta"
  insPolTypeEnv sigmaMeta tSigma
  bindSeq
    (zip nameList es)
    (Neg $ retMeta :< NegUpIntro (Pos $ sigmaMeta :< PosSigmaIntro nameList'))
polarizeNeg (meta :< NeutSigmaElim e1@(sigmaMeta :< _) xs e2) = do
  Neg e2' <- polarizeNeg e2
  z <- newNameWith "sigma"
  (_, retMeta) <- lookupTypeEnv' meta >>= polarizePos >>= toRetType'
  Pos tSigma <- lookupTypeEnv' sigmaMeta >>= polarizePos
  insPolTypeEnv sigmaMeta tSigma
  bindSeq
    [(z, e1)]
    (Neg $ retMeta :< NegSigmaElim (Pos $ sigmaMeta :< PosVar z) xs e2')
polarizeNeg e@(_ :< NeutBox _) = posRet e
polarizeNeg e@(_ :< NeutBoxIntro _) = posRet e
polarizeNeg (meta :< NeutBoxElim e@(boxMeta :< _)) = do
  z <- newNameWith "box"
  (_, retMeta) <- lookupTypeEnv' meta >>= polarizePos >>= toRetType'
  Pos boxType <- lookupTypeEnv' boxMeta >>= polarizePos
  insPolTypeEnv boxMeta boxType
  bindSeq
    [(z, e)]
    (Neg $
     retMeta :<
     (NegBoxElim $ retMeta :< NegDownElim (Pos $ boxMeta :< PosVar z)))
polarizeNeg t@(_ :< NeutIndex _) = posRet t
polarizeNeg e@(_ :< NeutIndexIntro _) = posRet e
polarizeNeg (meta :< NeutIndexElim e@(indexMeta :< _) branchList) = do
  let (labelList, es) = unzip branchList
  cs <- mapM polarizeNeg es
  let cs' = map toPreNeg cs
  x <- newName
  (_, retMeta) <- lookupTypeEnv' meta >>= polarizePos >>= toRetType'
  Pos indexType <- lookupTypeEnv' indexMeta >>= polarizePos
  insPolTypeEnv indexMeta indexType
  bindSeq
    [(x, e)]
    (Neg $
     retMeta :< NegIndexElim (Pos $ indexMeta :< PosVar x) (zip labelList cs'))
polarizeNeg (_ :< NeutMu _ _) = error "polarizeNeg.polarizeNeg: unreachable: Mu"
polarizeNeg t@(_ :< NeutUniv _) = do
  t' <- polarizePos t
  meta <- newNameWith "meta"
  return $ Neg $ meta :< NegUpIntro t'
polarizeNeg (_ :< NeutHole x) =
  error $ "PolarizeNeg.polarizeNeg: remaining hole: " ++ x

polarizePos :: Neut -> WithEnv Pos
polarizePos (meta :< NeutVar s) = do
  Pos t <- lookupTypeEnv' meta >>= polarizePos
  insPolTypeEnv meta t
  insPolTypeEnv s t
  return $ Pos $ meta :< PosVar s
polarizePos (meta :< NeutConst s _) = do
  Pos t <- lookupTypeEnv' meta >>= polarizePos
  insPolTypeEnv meta t
  insPolTypeEnv s t
  return $ Pos $ meta :< PosConst s
polarizePos (meta :< NeutPi (x, tdom) tcod) = do
  Pos tdom' <- polarizePos tdom
  insPolTypeEnv x tdom'
  Pos tcod' <- polarizePos tcod
  tcod'' <- wrap $ PosUp tcod'
  newMeta <- newNameWith "meta"
  return $ Pos $ newMeta :< (PosDown $ meta :< PosPi (x, tdom') tcod'')
polarizePos (meta :< NeutPiIntro (x, _) e) = do
  Neg e'@(eMeta :< _) <- polarizeNeg e
  Pos tx <- lookupTypeEnv' x >>= polarizePos
  insPolTypeEnv x tx
  eType <- lookupPolTypeEnv' eMeta
  lamMeta <- newNameWith "meta"
  tmp <- newNameWith "meta"
  insPolTypeEnv lamMeta $ tmp :< PosPi (x, tx) eType
  lookupTypeEnv' meta >>= polarizePos >>= \(Pos te) -> insPolTypeEnv meta te
  return $ Pos $ meta :< PosDownIntro (Neg $ lamMeta :< NegPiIntro x e')
polarizePos (_ :< NeutPiElim _ _) =
  lift $ throwE "Polarize.polarizePos.NeutPiElim"
polarizePos (meta :< NeutSigma xts body) = do
  Pos body' <- polarizePos body
  let (xs, ts) = unzip xts
  ts' <- mapM polarizePos ts
  let xts' = zip xs $ map toPrePos ts'
  forM_ xts' $ uncurry insPolTypeEnv
  return $ Pos $ meta :< PosSigma xts' body'
polarizePos (meta :< NeutSigmaIntro es) = do
  es' <- mapM polarizePos es
  let es'' = map toPrePos es'
  lookupTypeEnv' meta >>= polarizePos >>= \(Pos te) -> insPolTypeEnv meta te
  return $ Pos $ meta :< PosSigmaIntro es''
polarizePos (_ :< NeutSigmaElim {}) =
  lift $ throwE "Polarize.polarizePos.NeutSigmaElim"
polarizePos (meta :< NeutBox e) = do
  Pos e' <- polarizePos e
  e'' <- wrap $ PosUp e'
  return $ Pos $ meta :< PosBox e''
polarizePos (meta :< NeutBoxIntro e) = do
  e' <- polarizeNeg e
  lookupTypeEnv' meta >>= polarizePos >>= \(Pos te) -> insPolTypeEnv meta te
  return $ Pos $ meta :< PosBoxIntro e'
polarizePos (_ :< NeutBoxElim _) =
  lift $ throwE "Polarize.polarizePos.NeutBoxElim"
polarizePos (meta :< NeutIndex l) = return $ Pos $ meta :< PosIndex l
polarizePos (meta :< NeutIndexIntro l) = do
  Pos t <- lookupTypeEnv' meta >>= polarizePos
  insPolTypeEnv meta t
  case l of
    IndexLabel x -> do
      insPolTypeEnv x t
      return $ Pos $ meta :< PosIndexIntro l
    _ -> return $ Pos $ meta :< PosIndexIntro l
polarizePos (_ :< NeutIndexElim _ _) =
  lift $ throwE "Polarize.polarizePos.NeutIndexElim"
polarizePos (_ :< NeutMu _ _) = lift $ throwE "Polarize.polarizePos.NeutMu"
polarizePos (meta :< NeutUniv _) = return $ Pos $ meta :< PosUniv
polarizePos (_ :< NeutHole _) = lift $ throwE "Polarize.polarizePos.NeutHole"

bindSeq :: [(Identifier, Neut)] -> Neg -> WithEnv Neg
bindSeq [] fun = return fun
bindSeq ((formalArg, arg@(argMeta :< _)):rest) fun@(Neg (funMeta :< _)) = do
  Neg arg' <- polarizeNeg arg
  Neg fun' <- bindSeq rest fun
  argType <- lookupTypeEnv' argMeta
  insTypeEnv formalArg argType
  codType <- lookupPolTypeEnv' funMeta
  meta <- newNameOfPolType codType
  return $ Neg $ meta :< NegUpElim formalArg arg' fun'

toPrePos :: Pos -> PrePos
toPrePos (Pos e) = e

toPreNeg :: Neg -> PreNeg
toPreNeg (Neg e) = e

toRetType' :: Pos -> WithEnv (PrePos, Identifier)
toRetType' (Pos t) = toRetType t

toRetType :: PrePos -> WithEnv (PrePos, Identifier)
toRetType t = do
  tmp <- newNameWith "meta"
  let retType = tmp :< PosUp t
  retMeta <- newNameWith "meta"
  insPolTypeEnv retMeta retType
  return (tmp :< PosUp t, retMeta)

toPosVar :: Identifier -> WithEnv PrePos
toPosVar x = do
  Pos t <- lookupTypeEnv' x >>= polarizePos
  meta <- newNameWith "meta"
  insPolTypeEnv meta t
  return $ meta :< PosVar x

posRet :: Neut -> WithEnv Neg
posRet e@(meta :< _) = do
  e' <- polarizePos e
  (_, retMeta) <- lookupTypeEnv' meta >>= polarizePos >>= toRetType'
  return $ Neg $ retMeta :< NegUpIntro e'
