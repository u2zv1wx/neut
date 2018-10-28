-- This module generates a virtual code from a modal-normal term.
-- The procedure here is more or less straightforward. It would be worth noting that,
-- after the elimination of Sigma-terms in virtualComp, we insert CodeFree.
-- This can be justified that our type system is linear. Incidently, memory allocation
-- is trigerred before binding the content of `DataStruct ds` to a variable, which is
-- invisible at this stage.
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
virtualValue (ValueSigma _ _) = return $ DataInt 0
virtualValue (ValueSigmaIntro size es) = do
  ds <- mapM virtualValue es
  return $ DataStruct size ds
virtualValue (ValueIndex _) = return $ DataInt 0
virtualValue (ValueIndexIntro x meta) =
  case x of
    IndexDefault -> return $ DataInt 0
    IndexInteger i -> return $ DataInt i
    IndexFloat x -> do
      t <- lookupTypeEnv' meta
      case t of
        _ :< NeutIndex "f16" -> return $ DataFloat16 x
        _ :< NeutIndex "f32" -> return $ DataFloat32 x
        _ :< NeutIndex "f64" -> return $ DataFloat64 x
        _ ->
          lift $
          throwE $
          show x ++
          " is expected to be a valid floating point number, but its type is: " ++
          show t
    IndexLabel name -> do
      set <- lookupIndexSet name
      case elemIndex name set of
        Just i -> return $ DataInt i
        Nothing -> lift $ throwE $ "no such index defined: " ++ show name
virtualValue ValueUniv = return $ DataInt 0
virtualValue (ValueBox _) = return $ DataInt 0
virtualValue (ValueConst _) = return $ DataInt 0
virtualValue (ValueConstIntro x) = return $ DataGlobal x
virtualValue (ValueArith kind e1 e2) = do
  d1 <- virtualValue e1
  d2 <- virtualValue e2
  return $ DataArith kind d1 d2

virtualComp :: Comp -> WithEnv Code
virtualComp (CompPi _ _) = return $ CodeReturn $ DataInt 0
virtualComp (CompPiElimConstElim f xs) = do
  f' <- globalizeIfNecessary f
  let xs' = map DataLocal xs
  return $ CodeCallTail f' xs'
virtualComp (CompSigmaElim size e1 xs e2) = do
  e1' <- virtualValue e1
  e2' <- virtualComp e2
  case length xs of
    0 -> liftIO $ putStrLn "sigmaelim for empty"
    1 -> liftIO $ putStrLn "sigmaelim for singleton"
    _ -> return ()
  return $ extract e1' (zip xs [0 ..]) (length xs) size e2'
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
  return $ commUpElim x e1' e2'
virtualComp (CompPrint t e) = do
  e' <- virtualValue e
  return $ CodePrint t e' $ CodeReturn (DataInt 0)

extract :: Data -> [(Identifier, Int)] -> Int -> Int -> Code -> Code
extract z [] _ _ cont = CodeFree z cont
extract z ((x, i):xis) n size cont = do
  let cont' = extract z xis n size cont
  CodeExtractValue x z (i, n, size) cont'

-- Commutative conversion for up-elimination.
commUpElim :: String -> Code -> Code -> Code
commUpElim s (CodeReturn ans) cont = CodeLet s ans cont
commUpElim s (CodeLet x d cont1) cont2 = CodeLet x d (commUpElim s cont1 cont2)
commUpElim s (CodeCall reg name xds cont1) cont2 =
  CodeCall reg name xds $ commUpElim s cont1 cont2
commUpElim s (CodeCallTail name xds) cont = CodeCall s name xds cont
commUpElim x (CodeSwitch y branchList) cont = do
  let (labelList, es) = unzip branchList
  let es' = map (\e -> commUpElim x e cont) es
  CodeSwitch y $ zip labelList es'
commUpElim s (CodeExtractValue x basePointer i cont1) cont2 =
  CodeExtractValue x basePointer i $ commUpElim s cont1 cont2
commUpElim s (CodeFree x cont1) cont2 = CodeFree x $ commUpElim s cont1 cont2
commUpElim s (CodePrint t e' cont1) cont2 =
  CodePrint t e' (commUpElim s cont1 cont2)

globalizeIfNecessary :: Identifier -> WithEnv Data
globalizeIfNecessary x = do
  menv <- gets modalEnv
  if x `elem` map fst menv
    then return $ DataGlobal x
    else return $ DataLocal x
