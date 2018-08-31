module Emit
  ( emit
  ) where

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

import           Data.List

import           Debug.Trace

emit :: WithEnv ()
emit = do
  env <- get
  forM_ (codeEnv env) $ \(label, (args, body)) -> do
    funType <- lookupTypeEnv' label
    funType' <- unwrapDown funType
    let (codType, _) = forallArgs funType'
    argTypeList <- mapM lookupTypeEnv' args
    bodyAsm <- asmCode body
    emitDefine label codType (zip args argTypeList) bodyAsm
  forM_ (valueEnv env) $ \(label, _) -> do
    t <- lookupValueEnv' label
    t' <- unwrapDown t
    asm <- asmConstructor label t'
    let (codType, identTypeList) = forallArgs t'
    emitDefine label codType identTypeList asm

emitAsm :: Asm -> WithEnv ()
emitAsm (AsmReturn i) = do
  t <- lookupTypeEnv' i
  t' <- lookupLowTypeEnv' i
  -- liftIO $ putStrLn $ "the real type of " ++ i ++ " is " ++ show t'
  if t == t'
    then emitOp $ unwords ["ret", showType t, showRegister i]
    else do
      tmp <- newNameWith "cast"
      emitOp $
        unwords
          [ showRegister tmp
          , "="
          , "bitcast"
          , showType t'
          , showRegister i
          , "to"
          , showType t
          ]
      emitOp $ unwords ["ret", showType t, showRegister tmp]
emitAsm (AsmLet i op) = emitAsmLet i op
emitAsm (AsmStore (AsmDataRegister item) dest) = do
  itemType <- lookupTypeEnv' item
  destType <- lookupTypeEnv' dest
  emitOp $
    unwords
      [ "store"
      , showType itemType
      , showRegister item ++ ","
      , showType destType
      , showRegister dest
      ]
emitAsm (AsmStore (AsmDataFunName item) dest) = do
  destType <- lookupTypeEnv' dest
  emitOp $
    unwords
      [ "store"
      -- , showType itemType
      , "i8*"
      , showGlobal item ++ ","
      , showType destType
      , showRegister dest
      ]
emitAsm (AsmStore (AsmDataInt32 i) dest) = do
  let itemType = Fix $ TypeInt 32
  destType <- lookupTypeEnv' dest
  emitOp $
    unwords
      [ "store"
      , showType itemType
      , show i ++ ","
      , showType destType
      , showRegister dest
      ]
emitAsm (AsmSwitch i (defaultBranch, defaultCode) branchList) = do
  t <- lookupTypeEnv' i
  emitOp $
    unwords
      [ "switch"
      , showType t
      , showRegister i ++ ","
      , "label"
      , showRegister defaultBranch
      , "[" ++ showBranchList branchList ++ "]"
      ]
  let labelBranchList =
        (defaultBranch, defaultCode) : map toLabelAndAsm branchList
  forM_ labelBranchList $ \(label, asm) -> do
    emitLabelHeader label
    mapM emitAsm asm

emitAsmLet :: Identifier -> AsmOperation -> WithEnv ()
emitAsmLet i (AsmAlloc t) =
  emitOp $ unwords [showRegister i, "=", "alloca", showType t]
emitAsmLet i (AsmLoad source) = do
  ti <- lookupTypeEnv' i
  sourceType <- lookupTypeEnv' source
  emitOp $
    unwords
      [ showRegister i
      , "="
      , "load"
      , showType ti ++ ","
      , showType sourceType
      , showRegister source
      ]
emitAsmLet i (AsmGetElemPointer base index) = do
  baseType <- lookupLowTypeEnv' base
  case baseType of
    Fix (TypeDown t) ->
      emitOp $
      unwords
        [ showRegister i
        , "="
        , "getelementptr"
        , showType t ++ ","
        , showType baseType
        , showRegister base ++ ","
        , showIndex index
        ]
    t -> lift $ throwE $ "Emit.emitAsmLet.getelementptr. t:\n" ++ Pr.ppShow t
emitAsmLet i (AsmCall name args) = do
  funType <- lookupTypeEnv' name
  let (codType, _) = forallArgs funType
  argStr <- showArgs args
  emitOp $
    unwords
      [ showRegister i
      , "="
      , "call"
      , showType codType
      , showGlobal name
      , "(" ++ argStr ++ ")"
      ]
emitAsmLet i (AsmBitcast from ident to) =
  emitOp $
  unwords
    [showRegister i, "=", "bitcast", showType from, ident, "to", showType to]

showType :: Type -> String
showType (Fix TypeUnit) = "unit"
showType (Fix (TypeVar s)) = showRegister s
showType (Fix (TypeHole _)) = error "Emit.showType"
showType (Fix (TypeInt i)) = "i" ++ show i
showType (Fix (TypeUp t)) = showType t
showType (Fix (TypeDown t)) = showType t ++ "*"
showType (Fix (TypeUniv _)) = "<univ>"
showType t@(Fix (TypeForall _ _)) = do
  let (codType, identTypeList) = forallArgs t
  let typeList = map snd identTypeList
  "(" ++ unwords [showType codType, "(" ++ showTypeList typeList ++ ")"] ++ ")"
showType (Fix (TypeNode s _)) = showRegister s
showType (Fix TypeOpaque) = showRegister "any"
showType (Fix (TypeStruct ts)) = "{" ++ showTypeList ts ++ "}"

showArgs :: [Identifier] -> WithEnv String
showArgs [] = return ""
showArgs [i] = do
  t <- lookupTypeEnv' i
  return $ unwords [showType t, showRegister i]
showArgs (i:xs) = do
  t <- lookupTypeEnv' i
  s <- showArgs xs
  return $ unwords [showType t, showRegister i ++ ",", s]

showArgTypeList :: [(Identifier, Type)] -> String
showArgTypeList [] = ""
showArgTypeList [(i, t)] = unwords [showType t, showRegister i]
showArgTypeList ((i, t):xs) = do
  let s = showArgTypeList xs
  unwords [showType t, showRegister i ++ ",", s]

showRegister :: Identifier -> String
showRegister i = "%" ++ i

showGlobal :: Identifier -> String
showGlobal i = "@" ++ i

showTypeList :: [Type] -> String
showTypeList [] = ""
showTypeList [t] = showType t
showTypeList (t:ts) = do
  let s = showType t
  let ss = showTypeList ts
  s ++ ", " ++ ss

showIndex :: [Int] -> String
showIndex []     = ""
showIndex [i]    = "i32 " ++ show i
showIndex (i:is) = "i32 " ++ show i ++ ", " ++ showIndex is

showBranchList :: [AsmBranch] -> String
showBranchList [] = ""
showBranchList [(_, i, b, _)] = "i32 " ++ show i ++ ", label %" ++ b
showBranchList ((_, i, b, _):bs) =
  "i32 " ++ show i ++ ", label %" ++ b ++ " " ++ showBranchList bs

toLabelAndAsm :: AsmBranch -> (TargetLabel, [Asm])
toLabelAndAsm (_, _, label, asm) = (label, asm)

emitLabelHeader :: Identifier -> WithEnv ()
emitLabelHeader label = liftIO $ putStrLn $ label ++ ":"

emitOp :: String -> WithEnv ()
emitOp s = liftIO $ putStrLn $ "  " ++ s

emitDefine :: Identifier -> Type -> [(Identifier, Type)] -> [Asm] -> WithEnv ()
emitDefine name codType argList content = do
  liftIO $
    putStrLn $
    unwords
      [ "define"
      , showType codType
      , showGlobal name ++ "(" ++ showArgTypeList argList ++ ")"
      , "{"
      ]
  mapM_ emitAsm content
  liftIO $ putStrLn "}"
