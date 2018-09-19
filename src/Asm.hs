module Asm
  ( asmCodeEnv
  , asmCode
  ) where

import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.IORef

import           Data
import           Register

import           Control.Comonad.Cofree

import qualified Text.Show.Pretty           as Pr

import           Debug.Trace

asmCodeEnv :: WithEnv ()
asmCodeEnv = do
  env <- get
  forM_ (codeEnv env) $ \(name, (args, codeRef)) -> do
    code <- liftIO $ readIORef codeRef
    asm <- asmCode code
    liftIO $ putStrLn $ Pr.ppShow asm
    insAsmEnv name args asm

asmCode :: Code -> WithEnv Asm
asmCode (CodeReturn x) = return $ AsmReturn x
asmCode (CodeLet i d cont) = do
  cont' <- asmCode cont
  asmData i d cont'
asmCode (CodeCall x fun args cont) = do
  cont' <- asmCode cont
  return $ AsmCall x fun (map AsmArgReg args) cont'
asmCode (CodeExtractValue x base i cont) = do
  t <- lookupTypeEnv' base
  case t of
    _ :< NeutSigma _ _ -> do
      (_, args) <- toSigmaSeq t
      ts <- mapM (toLowType . snd) args
      cont' <- asmCode cont
      return $ AsmExtractValue x (base, LowTypeStruct ts) i cont'
    _ -> lift $ throwE "Asm.asmCode : typeError"

asmData :: Identifier -> Data -> Asm -> WithEnv Asm
asmData reg (DataLocal x) cont = return $ AsmLet reg (AsmArgReg x) cont
asmData reg (DataLabel x) cont = return $ AsmLet reg (AsmArgReg x) cont
asmData reg (DataInt32 i) cont = return $ AsmLet reg (AsmArgImmediate i) cont
asmData reg (DataStruct xs) cont = do
  ts <- mapM (lookupTypeEnv' >=> toLowType) xs
  cont' <- setContent ts reg (zip [0 ..] xs) cont
  return $ AsmMalloc reg (LowTypeStruct ts) cont'

setContent ::
     [LowType] -> Identifier -> [(Int, Identifier)] -> Asm -> WithEnv Asm
setContent _ _ [] cont = return cont
setContent ts basePointer ((index, d):sizeDataList) cont = do
  cont' <- setContent ts basePointer sizeDataList cont
  return $
    AsmInsertValue (AsmArgReg d) (basePointer, LowTypeStruct ts) index cont'
