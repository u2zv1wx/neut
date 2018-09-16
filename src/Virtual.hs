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
virtualPos (Pos (i :< PosForall _ _)) = virtualPos $ Pos $ i :< PosUnit
virtualPos (Pos (i :< PosExists _ _)) = virtualPos $ Pos $ i :< PosUnit
virtualPos (Pos (_ :< PosPair x y)) = return $ DataStruct [x, y]
virtualPos (Pos (i :< PosTop)) = virtualPos $ Pos $ i :< PosUnit
virtualPos (Pos (_ :< PosUnit)) = return $ DataInt32 0
virtualPos (Pos (i :< PosUp _)) = virtualPos $ Pos $ i :< PosUnit
virtualPos (Pos (i :< PosDown _)) = virtualPos $ Pos $ i :< PosUnit
virtualPos (Pos (i :< PosThunkLam args body)) = do
  bodyCode <- virtualNeg body
  name <- newNameWith "lam"
  lamType <- lookupPolTypeEnv' i
  insPolTypeEnv name lamType
  insCodeEnv name args bodyCode
  return $ DataLabel name
virtualPos (Pos (i :< PosUniv)) = virtualPos $ Pos $ i :< PosUnit

virtualNeg :: Neg -> WithEnv Code
virtualNeg (Neg (i :< NegAppForce funName args)) = do
  s <- newNameWith "tmp"
  resultType <- lookupPolTypeEnv' i
  insPolTypeEnv s resultType
  tmp <- addMeta $ CodeReturn $ DataLocal s
  addMeta $ CodeCall s funName args tmp
virtualNeg (Neg (_ :< NegCase z (x, y) e)) = do
  e' <- virtualNeg $ Neg e
  tmp <- addMeta $ CodeExtractValue y z 1 e'
  addMeta $ CodeExtractValue x z 0 tmp
virtualNeg (Neg (_ :< NegReturn v)) = do
  d <- virtualPos v
  x <- newName
  tmp <- addMeta $ CodeReturn $ DataLocal x
  addMeta $ CodeLet x d tmp
virtualNeg (Neg (_ :< NegBind x e1 e2)) = do
  e1' <- virtualNeg $ Neg e1
  e2' <- virtualNeg $ Neg e2
  traceLet x e1' e2'

traceLet :: String -> Code -> Code -> WithEnv Code
traceLet s (meta :< CodeReturn ans) cont = return $ meta :< CodeLet s ans cont
traceLet s (meta :< CodeLet k o1 o2) cont = do
  c <- traceLet s o2 cont
  return $ meta :< CodeLet k o1 c
traceLet s (meta :< CodeCall reg name xds cont1) cont2 = do
  tmp <- traceLet s cont1 cont2
  return $ meta :< CodeCall reg name xds tmp
traceLet s (meta :< CodeExtractValue x d i cont1) cont2 = do
  tmp <- traceLet s cont1 cont2
  return $ meta :< CodeExtractValue x d i tmp
traceLet s (meta :< CodeStackSave x cont1) cont2 = do
  tmp <- traceLet s cont1 cont2
  return $ meta :< CodeStackSave x tmp
traceLet s (meta :< CodeStackRestore x cont1) cont2 = do
  tmp <- traceLet s cont1 cont2
  return $ meta :< CodeStackRestore x tmp
