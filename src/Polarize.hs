module Polarize
  ( polarize
  ) where

import Control.Monad

import Control.Comonad.Cofree

import Control.Monad.State
import Control.Monad.Trans.Except

import qualified Text.Show.Pretty as Pr

import Data
import Reduce
import Util

import Data.Maybe (maybeToList)

polarize :: WithEnv ()
polarize = do
  wtenv <- gets weakTermEnv
  forM_ wtenv $ \(name, e) -> do
    e' <- polarizeNeg e
    insPolEnv name e'

polarizeNeg :: Neut -> WithEnv Neg
polarizeNeg (meta :< NeutVar x) = do
  retMeta <- newNameWith "meta"
  return $ Neg $ retMeta :< NegUpIntro (Pos $ meta :< PosVar x)
polarizeNeg (meta :< NeutConst x _) = do
  retMeta <- newNameWith "meta"
  return $ Neg $ retMeta :< NegUpIntro (Pos $ meta :< PosConst x)
polarizeNeg (meta :< NeutPi (x, tdom) tcod) = do
  dom <- newNameWith "dom"
  cod <- newNameWith "cod"
  bindSeq
    [(dom, tdom), (cod, tcod)]
    (Neg $
     meta :<
     NegUpIntro
       (Pos $
        meta :<
        PosDown
          (Neg $
           meta :<
           NegPi
             (x, Pos (meta :< PosVar dom))
             (meta :< NegUpIntro (Pos $ meta :< PosVar cod)))))
polarizeNeg (meta :< NeutPiIntro (x, _) e) = do
  Neg e' <- polarizeNeg e
  lamMeta <- newNameWith "meta"
  retMeta <- newNameWith "meta"
  return $
    Neg $
    retMeta :<
    NegUpIntro (Pos $ meta :< PosDownIntro (Neg $ lamMeta :< NegPiIntro x e'))
polarizeNeg (_ :< NeutPiElim e1@(meta1 :< _) e2@(meta2 :< _)) = do
  f <- newNameWith "pi"
  v <- newNameWith "arg"
  funMeta <- newNameWith "meta"
  retMeta <- newNameWith "meta"
  bindSeq
    [(v, e2), (f, e1)]
    (Neg $
     retMeta :<
     NegPiElim
       (funMeta :< NegDownElim (Pos $ meta1 :< PosVar f))
       (Pos $ meta2 :< PosVar v))
polarizeNeg (meta :< NeutSigma xts body) = do
  let (xs, ts) = unzip xts
  ys <- mapM (const (newNameWith "sigma")) xts
  vys <- mapM toPosVar ys
  z <- newNameWith "sigma"
  vz <- toPosVar z
  bindSeq
    (zip (ys ++ [z]) (ts ++ [body]))
    (Neg $ meta :< NegUpIntro (Pos $ meta :< PosSigma (zip xs vys) vz))
polarizeNeg (_ :< NeutSigmaIntro es) = do
  nameList <- mapM (const newName) es
  nameList' <- mapM toPosVar nameList
  retMeta <- newNameWith "meta"
  sigmaMeta <- newNameWith "meta"
  bindSeq
    (zip nameList es)
    (Neg $ retMeta :< NegUpIntro (Pos $ sigmaMeta :< PosSigmaIntro nameList'))
polarizeNeg (_ :< NeutSigmaElim e1@(sigmaMeta :< _) xs e2) = do
  Neg e2' <- polarizeNeg e2
  retMeta <- newNameWith "meta"
  z <- newNameWith "sigma"
  bindSeq
    [(z, e1)]
    (Neg $ retMeta :< NegSigmaElim (Pos $ sigmaMeta :< PosVar z) xs e2')
polarizeNeg (meta :< NeutBox e) = do
  e' <- polarizeNeg e
  return $ Neg $ meta :< NegUpIntro (Pos $ meta :< PosBox e')
polarizeNeg (meta :< NeutBoxIntro e) = do
  e' <- polarizeNeg e
  return $ Neg $ meta :< NegUpIntro (Pos $ meta :< PosBoxIntro e')
polarizeNeg (_ :< NeutBoxElim e@(boxMeta :< _)) = do
  retMeta <- newNameWith "meta"
  z <- newNameWith "box"
  bindSeq [(z, e)] (Neg $ retMeta :< (NegBoxElim $ Pos $ boxMeta :< PosVar z))
polarizeNeg (meta :< NeutIndex l) =
  return $ Neg $ meta :< NegUpIntro (Pos $ meta :< PosIndex l)
polarizeNeg (meta :< NeutIndexIntro l) =
  return $ Neg $ meta :< NegUpIntro (Pos $ meta :< PosIndexIntro l)
polarizeNeg (_ :< NeutIndexElim e@(indexMeta :< _) branchList) = do
  let (labelList, es) = unzip branchList
  cs <- mapM polarizeNeg es
  let cs' = map toPreNeg cs
  retMeta <- newNameWith "meta"
  x <- newNameWith "tmp"
  bindSeq
    [(x, e)]
    (Neg $
     retMeta :< NegIndexElim (Pos $ indexMeta :< PosVar x) (zip labelList cs'))
polarizeNeg (_ :< NeutMu _ _) = error "polarizeNeg.polarizeNeg: unreachable: Mu"
polarizeNeg (_ :< NeutUniv _) = do
  meta <- newNameWith "meta"
  return $ Neg $ meta :< NegUpIntro (Pos $ meta :< PosUniv)
polarizeNeg (_ :< NeutHole x) =
  error $ "PolarizeNeg.polarizeNeg: remaining hole: " ++ x

bindSeq :: [(Identifier, Neut)] -> Neg -> WithEnv Neg
bindSeq [] fun = return fun
bindSeq ((formalArg, arg):rest) fun = do
  Neg arg' <- polarizeNeg arg
  Neg fun' <- bindSeq rest fun
  meta <- newNameWith "meta"
  return $ Neg $ meta :< NegUpElim formalArg arg' fun'

toPreNeg :: Neg -> PreNeg
toPreNeg (Neg e) = e

toPosVar :: Identifier -> WithEnv PrePos
toPosVar x = do
  meta <- newNameWith "meta"
  return $ meta :< PosVar x
