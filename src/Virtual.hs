module Virtual
  ( virtualValue
  , virtualComp
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

import Data.Maybe (fromMaybe)

import qualified Text.Show.Pretty as Pr

import Debug.Trace

virtualValue :: Value -> WithEnv Data
virtualValue (Value (_ :< ValueVar x)) = return $ DataLocal x
virtualValue (Value (_ :< ValueConst x)) = return $ DataLabel x
virtualValue (Value (_ :< ValuePi _ _)) = return $ DataInt32 0
virtualValue (Value (_ :< ValueSigma _ _)) = return $ DataInt32 0
virtualValue (Value (_ :< ValueSigmaIntro es)) = do
  ds <- mapM (virtualValue . Value) es
  ts <- mapM (\(meta :< _) -> lookupValueTypeEnv' meta) es
  return $ DataStruct $ zip ds ts
virtualValue (Value (_ :< ValueIndex _)) = return $ DataInt32 0
virtualValue (Value (_ :< ValueIndexIntro x)) = do
  i <- indexToInt x
  return $ DataInt32 i
virtualValue (Value (_ :< ValueUp _)) = return $ DataInt32 0
virtualValue (Value (_ :< ValueUniv)) = return $ DataInt32 0

virtualComp :: Comp -> WithEnv Code
virtualComp (Comp (_ :< CompPiElim f xs)) = do
  let f' = DataLocal f
  tf <- lookupValueTypeEnv' f
  let xs' = map DataLocal xs
  ts <- mapM lookupValueTypeEnv' xs
  return $ CodeCallTail (f', tf) (zip xs' ts)
virtualComp (Comp (_ :< CompSigmaElim e1@(Value (meta1 :< _)) xs e2)) = do
  e1' <- virtualValue e1
  t1 <- lookupValueTypeEnv' meta1
  e2' <- virtualComp $ Comp e2
  return $ extract (e1', t1) (zip xs [0 ..]) e2'
virtualComp (Comp (_ :< CompIndexElim e@(Value (meta :< _)) branchList)) = do
  let (labelList, es) = unzip branchList
  es' <- mapM (virtualComp . Comp) es
  e' <- virtualValue e
  te <- lookupValueTypeEnv' meta
  return $ CodeSwitch (e', te) $ zip labelList es'
virtualComp (Comp (meta :< CompUpIntro v)) = do
  d <- virtualValue v
  t <- lookupValueTypeEnv' meta
  return $ CodeReturn (d, t)
virtualComp (Comp (_ :< CompUpElim x e1 e2)) = do
  e1' <- virtualComp $ Comp e1
  e2' <- virtualComp $ Comp e2
  return $ traceLet x e1' e2'

extract :: DataPlus -> [(Identifier, Int)] -> Code -> Code
extract z [] cont = CodeFree z cont
extract z ((x, i):xis) cont = do
  let cont' = extract z xis cont
  CodeExtractValue x z i cont'

traceLet :: String -> Code -> Code -> Code
traceLet s (CodeReturn (ans, _)) cont = substCode [(s, ans)] cont
traceLet s (CodeCall reg name xds cont1) cont2 =
  CodeCall reg name xds $ traceLet s cont1 cont2
traceLet s (CodeCallTail name xds) cont = CodeCall s name xds cont
traceLet x (CodeSwitch y branchList) cont = do
  let (labelList, es) = unzip branchList
  let es' = map (\e -> traceLet x e cont) es
  CodeSwitch y $ zip labelList es'
traceLet s (CodeExtractValue x basePointer i cont1) cont2 =
  CodeExtractValue x basePointer i $ traceLet s cont1 cont2
traceLet s (CodeFree x cont1) cont2 = CodeFree x $ traceLet s cont1 cont2
