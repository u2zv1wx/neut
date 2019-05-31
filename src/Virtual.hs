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
  -- cenv <- gets codeEnv
  -- forM_ cenv $ \(name, (args, e)) -> do
  --   liftIO $ putStrLn name
  --   liftIO $ print args
  --   liftIO $ putStrLn $ Pr.ppShow e
  --   liftIO $ putStrLn "-----------------------------"

virtualValue :: Value -> WithEnv Data
virtualValue (ValueVar x) = return $ DataLocal x
virtualValue (ValueConst x) = return $ DataGlobal x
virtualValue (ValueSigmaIntro es) = do
  ds <- mapM virtualValue es
  return $ DataStruct ds
virtualValue (ValueIndexIntro x meta) =
  case x of
    IndexDefault -> return $ DataInt 0
    IndexInteger i -> return $ DataInt i
    IndexFloat x -> do
      t <- lookupTypeEnv' meta >>= reduce
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

virtualComp :: Comp -> WithEnv Code
virtualComp (CompPiElimDownElim f vs) = do
  ds <- mapM virtualValue vs
  return $ CodeCallTail (DataLocal f) ds
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
  return $ commUpElim x e1' e2'
virtualComp (CompConstElim f xs) =
  case f of
    ConstantPrint lowType
      | length xs == 1 -> do
        let xs' = map DataLocal xs
        return $ CodePrint lowType (head xs') $ CodeReturn (DataInt 0)
    ConstantArith lowType kind
      | length xs == 2 -> do
        let xs' = map DataLocal xs
        return $ CodeReturn (DataArith (kind, lowType) (head xs') (xs' !! 1))
    _ ->
      lift $
      throwE $ "Arith mismatch for " ++ show f ++ " with xs = " ++ show xs

extract :: Data -> [(Identifier, Int)] -> Int -> Code -> Code
extract z [] _ cont = CodeFree z cont
extract z ((x, i):xis) n cont =
  CodeExtractValue x z (i, n) $ extract z xis n cont

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
commUpElim s (CodePrint x d cont1) cont2 =
  CodePrint x d (commUpElim s cont1 cont2)
