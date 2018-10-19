module Virtual
  ( virtualize
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

virtualize :: WithEnv ()
virtualize = do
  menv <- gets modalEnv
  forM_ menv $ \(name, (args, code)) -> do
    code' <- virtualComp code
    insCodeEnv name args code'

virtualValue :: Value -> WithEnv Data
virtualValue (ValueVar x) = globalizeIfNecessary x
virtualValue (ValueConst x) = return $ DataGlobal x
virtualValue (ValueSigma _ _) = return $ DataInt32 0
virtualValue (ValueSigmaIntro es) = do
  ds <- mapM virtualValue es
  return $ DataStruct ds
virtualValue (ValueIndex _) = return $ DataInt32 0
virtualValue (ValueIndexIntro x) = do
  i <- indexToInt x
  return $ DataInt32 i
virtualValue ValueUniv = return $ DataInt32 0
virtualValue (ValueBox _) = return $ DataInt32 0
virtualValue (ValueArith kind e1 e2) = do
  d1 <- virtualValue e1
  d2 <- virtualValue e2
  return $ DataArith kind d1 d2

virtualComp :: Comp -> WithEnv Code
virtualComp (CompPi _ _) = return $ CodeReturn $ DataInt32 0
virtualComp (CompPiElim f xs) = do
  f' <- globalizeIfNecessary f
  let xs' = map DataLocal xs
  return $ CodeCallTail f' xs'
virtualComp (CompSigmaElim e1 xs e2) = do
  e1' <- virtualValue e1
  e2' <- virtualComp e2
  return $ extract e1' (zip xs [0 ..]) (length xs) e2'
virtualComp (CompIndexElim e branchList) = do
  let (labelList, es) = unzip branchList
  es' <- mapM virtualComp es
  e' <- virtualValue e
  return $ CodeSwitch e' $ zip labelList es'
virtualComp (CompUpIntro v) = do
  d <- virtualValue v
  return $ CodeReturn d
virtualComp (CompUpElim x e1 e2) = do
  e1' <- virtualComp e1
  e2' <- virtualComp e2
  return $ traceLet x e1' e2'

extract :: Data -> [(Identifier, Int)] -> Int -> Code -> Code
extract z [] _ cont = CodeFree z cont
extract z ((x, i):xis) n cont = do
  let cont' = extract z xis n cont
  CodeExtractValue x z (i, n) cont'

traceLet :: String -> Code -> Code -> Code
traceLet s (CodeReturn ans) cont = CodeLet s ans cont
traceLet s (CodeLet x d cont1) cont2 = CodeLet x d (traceLet s cont1 cont2)
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

globalizeIfNecessary :: Identifier -> WithEnv Data
globalizeIfNecessary x = do
  menv <- gets modalEnv
  if x `elem` map fst menv
    then return $ DataGlobal x
    else return $ DataLocal x
