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
  liftIO $ putStrLn "define void @main() {"
  -- exitLabel <- newNameWith "exit"
  forM_ (funEnv env) $ \(label, codeRef) -> do
    code <- liftIO $ readIORef codeRef
    emitLabelHeader label
    emitCode code
  emitLabelHeader "exit"
  emitOp $ "ret void"
  liftIO $ putStrLn "}"

emitCode :: Code -> WithEnv ()
emitCode (CodeMeta {codeMetaArgs = xds@(_:_)} :< code) = do
  let (xs, ds) = unzip xds
  code' <- addMeta code
  tmp <- letSeq xs ds code'
  emitCode tmp
emitCode (_ :< CodeReturn retReg label d) = do
  x <- emitData d
  emitOp $ "%" ++ retReg ++ " = " ++ x
  emitOp $ "br label %" ++ label
emitCode (_ :< CodeLet i (Fix (DataLabel label)) cont) = do
  emitOp $ "%" ++ i ++ " = alloca label"
  emitOp $ "store label %" ++ label ++ ", label* %" ++ i
  emitCode cont
emitCode (_ :< CodeLet i (Fix (DataPointer x)) cont) = do
  emitOp $ "%" ++ i ++ " = load <type>, <type>* %" ++ x
  emitCode cont
emitCode (_ :< CodeLet i d cont) = do
  x <- emitData d
  emitOp $ "%" ++ i ++ " = " ++ x
  emitCode cont
emitCode (_ :< CodeLetLink i d cont) = do
  x <- emitData d
  emitOp $ "%" ++ i ++ " = " ++ x
  emitCode cont
emitCode (_ :< CodeSwitch x defaultBranch branchList) = do
  emitOp $
    "switch i32 " ++
    "%" ++
    x ++
    ", label %" ++ defaultBranch ++ " [" ++ emitBranchList branchList ++ "]"
emitCode (_ :< CodeJump label) = emitOp $ "br label %" ++ label
emitCode (_ :< CodeIndirectJump x unthunkId poss) =
  emitOp $ "indirectbr label %" ++ x ++ ", [" ++ show poss ++ "]"
emitCode (_ :< CodeRecursiveJump x) =
  emitOp $ "indirectbr label %" ++ x ++ ", [" ++ show x ++ "]"
emitCode (_ :< CodeStackSave stackReg cont) = do
  emitOp $ "%" ++ stackReg ++ " = call i8* @llvm.stacksave()"
  emitCode cont
emitCode (_ :< CodeStackRestore stackReg cont) = do
  emitOp $ "call void @llvm.stackrestore(i8* " ++ "%" ++ stackReg ++ ")"
  emitCode cont

emitData :: UData -> WithEnv String
emitData (Fix (DataPointer x)) = return $ "%" ++ x
emitData (Fix (DataCell s ds)) = do
  ss <- mapM emitData ds
  return $ s ++ " [" ++ join ss ++ "]"
emitData (Fix (DataLabel label)) = return $ "%" ++ label
emitData (Fix (DataElemAtIndex d [])) = emitData d
emitData (Fix (DataElemAtIndex d idx)) = do
  tmp <- emitData d
  return $ "getelementptr <ty>, <ty>* " ++ tmp ++ ", " ++ emitIndex idx ++ ""

emitIndex :: [Int] -> String
emitIndex []     = ""
emitIndex [i]    = "i32 " ++ show i
emitIndex (i:is) = "i32 " ++ show i ++ emitIndex is

emitBranchList :: [Branch] -> String
emitBranchList []          = ""
emitBranchList [(_, b)]    = "%" ++ b
emitBranchList ((_, b):bs) = "%" ++ b ++ ", " ++ emitBranchList bs

emitLabelHeader :: Identifier -> WithEnv ()
emitLabelHeader label = liftIO $ putStrLn $ label ++ ":"

emitOp :: String -> WithEnv ()
emitOp s = liftIO $ putStrLn $ "  " ++ s
