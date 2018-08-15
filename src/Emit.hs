module Emit where

import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.IORef

import           Asm
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
    asm <- asmCode code
    emitLabelHeader label
    emitAsm asm
  emitLabelHeader "exit"
  emitOp $ "ret void"
  liftIO $ putStrLn "}"

emitAsm :: Asm -> WithEnv ()
emitAsm (AsmLet i op cont) = emitAsmLet i op cont
emitAsm (AsmStore t item dest cont) = do
  emitOp $
    "store " ++ showType t ++ " " ++ item ++ ", " ++ showType t ++ "* " ++ dest
  emitAsm cont
emitAsm (AsmBranch label) = do
  emitOp $ "br label %" ++ label
emitAsm (AsmIndirectBranch label poss) = do
  emitOp $ "indirectbr label %" ++ label ++ ", [" ++ showPossDest poss ++ "]"
emitAsm (AsmSwitch i defaultBranch branchList) = do
  emitOp $
    "switch i32 " ++
    "%" ++
    i ++
    ", label %" ++ defaultBranch ++ " [" ++ showBranchList branchList ++ "]"

emitAsmLet :: Identifier -> AsmOperation -> Asm -> WithEnv ()
emitAsmLet i (AsmAlloc t) cont = do
  emitOp $ "%" ++ i ++ " = alloca " ++ showType t
  emitAsm cont
emitAsmLet i (AsmLoad t source) cont = do
  emitOp $
    "%" ++
    i ++ " = load " ++ showType t ++ ", " ++ showType t ++ "* %" ++ source
  emitAsm cont
emitAsmLet i (AsmGetElemPointer t base index) cont = do
  emitOp $
    "%" ++
    i ++
    " = getelementptr " ++
    showType t ++
    ", " ++ showType t ++ "* %" ++ base ++ ", i32 0, " ++ showIndex index
  emitAsm cont
emitAsmLet i AsmStackSave cont = do
  emitOp $ "%" ++ i ++ " = call i8* @llvm.stacksave()"
  emitAsm cont
emitAsmLet i AsmStackRestore cont = do
  emitOp $ "call void @llvm.stackrestore(i8* " ++ "%" ++ i ++ ")"
  emitAsm cont

showPossDest :: [Identifier] -> String
showPossDest []     = ""
showPossDest [d]    = "label " ++ show d
showPossDest (d:ds) = "label " ++ show d ++ ", " ++ showPossDest ds

showType :: LowType -> String
showType LowTypeInt32 = "i32"
showType LowTypeNull = "null"
showType (LowTypeStruct (ts)) = do
  let tmp = showTypeList ts
  "{" ++ tmp ++ "}"
showType LowTypeLabel = "label"
showType (LowTypePointer t) = do
  let s = showType t
  s ++ "*"

showTypeList :: [LowType] -> String
showTypeList [] = ""
showTypeList [t] = do
  showType t
showTypeList (t:ts) = do
  let s = showType t
  let ss = showTypeList ts
  s ++ ", " ++ ss

showIndex :: [Int] -> String
showIndex []     = ""
showIndex [i]    = "i32 " ++ show i
showIndex (i:is) = "i32 " ++ show i ++ ", " ++ showIndex is

showBranchList :: [Branch] -> String
showBranchList []          = ""
showBranchList [(_, b)]    = "<num> %" ++ b
showBranchList ((_, b):bs) = "<num> " ++ "%" ++ b ++ ", " ++ showBranchList bs

emitLabelHeader :: Identifier -> WithEnv ()
emitLabelHeader label = liftIO $ putStrLn $ label ++ ":"

emitOp :: String -> WithEnv ()
emitOp s = liftIO $ putStrLn $ "  " ++ s
