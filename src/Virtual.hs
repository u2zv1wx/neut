module Virtual
  ( virtualPos
  , virtualNeg
  ) where

import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Data

import           Control.Comonad.Cofree

import qualified Text.Show.Pretty           as Pr

import           Debug.Trace

virtualPos :: Pos -> WithEnv Data
virtualPos (Pos (_ :< PosVar x)) = return (DataLocal x)
virtualPos (Pos (i :< PosPi _ _)) = virtualPos $ Pos $ i :< PosTopIntro
virtualPos (Pos (i :< PosSigma _ _)) = virtualPos $ Pos $ i :< PosTopIntro
virtualPos (Pos (_ :< PosSigmaIntro xs)) = return $ DataStruct xs
virtualPos (Pos (i :< PosTop)) = virtualPos $ Pos $ i :< PosTopIntro
virtualPos (Pos (_ :< PosTopIntro)) = return $ DataInt32 0
virtualPos (Pos (i :< PosUp _)) = virtualPos $ Pos $ i :< PosTopIntro
virtualPos (Pos (i :< PosDown _)) = virtualPos $ Pos $ i :< PosTopIntro
virtualPos (Pos (i :< PosDownIntroPiIntro args body)) = do
  bodyCode <- virtualNeg body
  name <- newNameWith "lam"
  lamType <- lookupPolTypeEnv' i
  insPolTypeEnv name lamType
  insCodeEnv name args bodyCode
  return $ DataLabel name
virtualPos (Pos (i :< PosUniv _)) = virtualPos $ Pos $ i :< PosTopIntro

virtualNeg :: Neg -> WithEnv Code
virtualNeg (Neg (i :< NegPiElimDownElim funName args)) = do
  s <- newNameWith "tmp"
  resultType <- lookupPolTypeEnv' i
  insPolTypeEnv s resultType
  return $ CodeCall s funName args (CodeReturn $ DataLocal s)
virtualNeg (Neg (_ :< NegSigmaElim z (x, y) e)) = do
  e' <- virtualNeg $ Neg e
  return $ CodeExtractValue x z 0 (CodeExtractValue y z 1 e')
virtualNeg (Neg (_ :< NegUpIntro v)) = do
  d <- virtualPos v
  x <- newName
  return $ CodeLet x d (CodeReturn $ DataLocal x)
virtualNeg (Neg (_ :< NegUpElim x e1 e2)) = do
  e1' <- virtualNeg $ Neg e1
  e2' <- virtualNeg $ Neg e2
  traceLet x e1' e2'

traceLet :: String -> Code -> Code -> WithEnv Code
traceLet s (CodeReturn ans) cont = return $ CodeLet s ans cont
traceLet s (CodeLet k o1 o2) cont = do
  c <- traceLet s o2 cont
  return $ CodeLet k o1 c
traceLet s (CodeCall reg name xds cont1) cont2 = do
  tmp <- traceLet s cont1 cont2
  return $ CodeCall reg name xds tmp
traceLet s (CodeExtractValue x d i cont1) cont2 = do
  tmp <- traceLet s cont1 cont2
  return $ CodeExtractValue x d i tmp
