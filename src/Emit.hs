module Emit
  ( emit
  ) where

import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.IORef

import           Data

import           Control.Comonad.Cofree

import qualified Text.Show.Pretty           as Pr

import           Data.List

import           Debug.Trace

emit :: WithEnv ()
emit = do
  env <- get
  forM_ (codeEnv env) $ \(label, (args, body)) -> do
    let (codType, _) = undefined
    -- funType <- lookupPolTypeEnv' label
    -- funType' <- unwrapDown funType
    -- let (codType, _) = forallArgs funType'
    argTypeList <- mapM lookupPolTypeEnv' args
    -- bodyAsm <- asmCode body
    emitDefine label codType (zip args argTypeList) body

emitAsm :: Code -> WithEnv ()
emitAsm (CodeReturn d) = do
  t <- typeOfData d
  emitOp $ unwords ["ret", showType t, showData d]
emitAsm (CodeLet x d cont) = do
  let cont' = substCode [(x, d)] cont
  emitAsm cont'
emitAsm (CodeCall x fun args cont) = do
  codType <- lookupPolTypeEnv' x
  argStr <- showArgs args
  emitOp $
    unwords
      [ showLocal x
      , "="
      , "call"
      , showType codType
      , showData fun
      , "(" ++ argStr ++ ")"
      ]
  emitAsm cont
emitAsm (CodeExtractValue i base index cont) = do
  baseType <- typeOfData base
  emitOp $
    unwords
      [ showLocal i
      , "="
      , "extractvalue"
      , showType baseType
      , showData base ++ ","
      , show index
      ]
  emitAsm cont

typeOfData :: Data -> WithEnv Pos
typeOfData d = undefined

showData :: Data -> String
showData = undefined

showType :: Pos -> String
showType = undefined

-- showType (_ :< TypeUnit) = "unit"
-- showType (_ :< (TypeVar s)) = showLocal s
-- showType (_ :< (TypeHole _)) = error "Emit.showType"
-- showType (_ :< (TypeInt i)) = "i" ++ show i
-- showType (_ :< (TypeUp t)) = showType t
-- showType (_ :< (TypeDown t)) = showType t ++ "*"
-- showType (_ :< (TypeUniv _)) = "<univ>"
-- showType t@(_ :< (TypeForall _ _)) = do
--   let (codType, identTypeList) = forallArgs t
--   let typeList = map snd identTypeList
--   "(" ++ unwords [showType codType, "(" ++ showTypeList typeList ++ ")"] ++ ")"
-- showType (_ :< (TypeNode s _)) = showLocal s
-- showType (_ :< (TypeStruct ts)) = "{" ++ showTypeList ts ++ "}"
showArgs :: [Data] -> WithEnv String
showArgs [] = return ""
showArgs [i] = do
  t <- typeOfData i
  return $ unwords [showType t, showData i]
showArgs (i:xs) = do
  t <- typeOfData i
  s <- showArgs xs
  return $ unwords [showType t, showData i ++ ",", s]

showArgTypeList :: [(Identifier, Pos)] -> String
showArgTypeList [] = ""
showArgTypeList [(i, t)] = unwords [showType t, showLocal i]
showArgTypeList ((i, t):xs) = do
  let s = showArgTypeList xs
  unwords [showType t, showLocal i ++ ",", s]

showLocal :: Identifier -> String
showLocal i = "%" ++ i

showGlobal :: Identifier -> String
showGlobal i = "@" ++ i

showTypeList :: [Pos] -> String
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

emitOp :: String -> WithEnv ()
emitOp s = liftIO $ putStrLn $ "  " ++ s

emitDefine :: Identifier -> Pos -> [(Identifier, Pos)] -> Code -> WithEnv ()
emitDefine name codType argList content = do
  liftIO $
    putStrLn $
    unwords
      [ "define"
      , showType codType
      , showGlobal name ++ "(" ++ showArgTypeList argList ++ ")"
      , "{"
      ]
  emitAsm content
  liftIO $ putStrLn "}"
