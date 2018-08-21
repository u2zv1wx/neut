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
  forM_ (codeEnv env) $ \(label, codeListRef) -> do
    t <- lookupLowTypeEnv' label
    case t of
      LowTypeLabel (LowTypeFunction args cod) -> do
        liftIO $
          putStrLn $
          "define " ++
          showType cod ++ " @" ++ label ++ "(" ++ showArgs args ++ ") {"
        codeList <- liftIO $ readIORef codeListRef
        forM_ codeList $ \(label, codeRef) -> do
          code <- liftIO $ readIORef codeRef
          asm <- asmCode code
          emitLabelHeader label
          mapM_ emitAsm asm
        liftIO $ putStrLn "}"
      t -> do
        liftIO $ putStrLn $ "define " ++ showType t ++ " @" ++ label ++ "() {"
        codeList <- liftIO $ readIORef codeListRef
        forM_ codeList $ \(label, codeRef) -> do
          code <- liftIO $ readIORef codeRef
          asm <- asmCode code
          emitLabelHeader label
          mapM_ emitAsm asm
        liftIO $ putStrLn "}"

emitAsm :: Asm -> WithEnv ()
emitAsm (AsmReturn (i, t)) = emitOp $ "ret " ++ showType t ++ " %" ++ i
emitAsm (AsmLet i op) = emitAsmLet i op
emitAsm (AsmStore t (AsmDataRegister item) dest) = do
  emitOp $
    "store " ++
    showType t ++ " %" ++ item ++ ", " ++ showType t ++ "* %" ++ dest
emitAsm (AsmStore t (AsmDataLabel item) dest) = do
  emitOp $
    "store " ++
    showType t ++
    " blockaddress(@main, %" ++ item ++ "), " ++ showType t ++ "* %" ++ dest
emitAsm (AsmStore t (AsmDataInt i) dest) = do
  emitOp $
    "store " ++
    showType t ++ " " ++ show i ++ ", " ++ showType t ++ "* %" ++ dest
emitAsm (AsmBranch label) = do
  emitOp $ "br label %" ++ label
emitAsm (AsmIndirectBranch label poss) = do
  emitOp $ "indirectbr label %" ++ label ++ ", [" ++ showPossDest poss ++ "]"
emitAsm (AsmSwitch i defaultBranch branchList) = do
  t <- lookupLowTypeEnv' i
  emitOp $
    "switch " ++
    showType t ++
    " %" ++
    i ++
    ", label %" ++ defaultBranch ++ " [" ++ showBranchList branchList ++ "]"

--    "switch i32 " ++
emitAsmLet :: Identifier -> AsmOperation -> WithEnv ()
emitAsmLet i (AsmAlloc t) = do
  emitOp $ "%" ++ i ++ " = alloca " ++ showType t
emitAsmLet i (AsmLoad t source) = do
  let t' = traceType [0] t
  emitOp $
    "%" ++
    i ++ " = load " ++ showType t' ++ ", " ++ showType t ++ " %" ++ source
emitAsmLet i (AsmGetElemPointer t base index) = do
  let t' = traceType [0] t
  emitOp $
    "%" ++
    i ++
    " = getelementptr " ++
    showType t' ++ ", " ++ showType t ++ " %" ++ base ++ ", " ++ showIndex index
emitAsmLet i (AsmCall (name, codType) args) = do
  emitOp $
    "%" ++
    i ++
    " = call " ++
    showType codType ++ " @" ++ name ++ "(" ++ showArgs args ++ ")"
emitAsmLet i (AsmBitcast from ident to) = do
  emitOp $
    "%" ++
    i ++ " = bitcast " ++ showType from ++ " " ++ ident ++ " to " ++ showType to

showPossDest :: [Identifier] -> String
showPossDest []     = ""
showPossDest [d]    = "label " ++ show d
showPossDest (d:ds) = "label " ++ show d ++ ", " ++ showPossDest ds

showType :: LowType -> String
showType LowTypeInt32 = "i32"
showType LowTypeInt8 = "i8"
showType LowTypeNull = "null"
showType (LowTypeStruct (ts)) = do
  let tmp = showTypeList ts
  "{" ++ tmp ++ "}"
showType (LowTypeLabel _) = "<label>"
showType (LowTypePointer t) = do
  let s = showType t
  s ++ "*"
showType LowTypeAny = "%any"

showArgs :: [(Identifier, LowType)] -> String
showArgs []          = ""
showArgs [(i, t)]    = showType t ++ " %" ++ i
showArgs ((i, t):xs) = showType t ++ " %" ++ i ++ ", " ++ showArgs xs

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
showBranchList [] = ""
showBranchList [(_, i, b)] = do
  "i32 " ++ show i ++ ", label %" ++ b
showBranchList ((_, i, b):bs) = do
  "i32 " ++ show i ++ ", label %" ++ b ++ " " ++ showBranchList bs

emitLabelHeader :: Identifier -> WithEnv ()
emitLabelHeader label = liftIO $ putStrLn $ label ++ ":"

emitOp :: String -> WithEnv ()
emitOp s = liftIO $ putStrLn $ "  " ++ s
