module Emit where

import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.IORef

import           Data

import           Control.Comonad.Cofree

import qualified Text.Show.Pretty           as Pr

import           Debug.Trace

emit :: WithEnv ()
emit = do
  env <- get
  liftIO $ putStrLn "define <type> @main() {"
  forM_ (funEnv env) $ \(label, codeRef) -> do
    code <- liftIO $ readIORef codeRef
    emitLabelHeader label
    emitCode code
  liftIO $ putStrLn "}"

emitCode :: Code -> WithEnv ()
emitCode (CodeMeta {codeMetaArgs = xds@(_:_)} :< code) = do
  let (xs, ds) = unzip xds
  code' <- addMeta code
  tmp <- letSeq xs ds code'
  emitCode tmp
emitCode (_ :< CodeReturn retReg linkReg d) = do
  emitOp $ "%" ++ retReg ++ " = " ++ emitData d
  emitOp $ "indirectbr label %" ++ linkReg
emitCode (_ :< CodeLet i d cont) = do
  emitOp $ "%" ++ i ++ " = " ++ emitData d
  emitCode cont
emitCode (_ :< CodeLetLink i d cont) = do
  emitOp $ "%" ++ i ++ " = " ++ emitData d
  emitCode cont
emitCode (_ :< CodeSwitch x defaultBranch branchList) = do
  emitOp $
    "switch i32 " ++
    "%" ++
    x ++
    ", label %" ++ defaultBranch ++ " [" ++ emitBranchList branchList ++ "]"
emitCode (_ :< CodeJump label) = emitOp $ "br label %" ++ label
emitCode (_ :< CodeIndirectJump x) = emitOp $ "indirectbr label %" ++ x
emitCode (_ :< CodeStackSave stackReg cont) = do
  emitOp $ "%" ++ stackReg ++ " = call i8* @llvm.stacksave()"
  emitCode cont
emitCode (_ :< CodeStackRestore stackReg cont) = do
  emitOp $ "call void @llvm.stackrestore(i8* " ++ "%" ++ stackReg ++ ")"
  emitCode cont

emitData :: UData -> String
emitData (Fix (DataPointer x)) = "%" ++ x
emitData (Fix (DataCell s ds)) = s ++ " [" ++ join (map emitData ds) ++ "]"
emitData (Fix (DataLabel label)) = "%" ++ label
emitData (Fix (DataElemAtIndex d [])) = emitData d
emitData (Fix (DataElemAtIndex d idx)) =
  "getelementptr <ty>, <ty>* " ++ emitData d ++ ", " ++ emitIndex idx ++ ""

emitIndex :: [Int] -> String
emitIndex []     = ""
emitIndex [i]    = "i32 " ++ show i
emitIndex (i:is) = "i32 " ++ show i ++ emitIndex is

emitBranchList :: [Branch] -> String
emitBranchList []          = ""
emitBranchList [(_, b)]    = "%" ++ b
emitBranchList ((c, b):bs) = "%" ++ b ++ ", " ++ emitBranchList bs

emitLabelHeader :: Identifier -> WithEnv ()
emitLabelHeader label = liftIO $ putStrLn $ label ++ ":"

emitOp :: String -> WithEnv ()
emitOp s = liftIO $ putStrLn $ "  " ++ s
