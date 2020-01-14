{-# LANGUAGE FlexibleInstances #-}

module Data.Env where

import Control.Monad.Except
import Control.Monad.State
import Path
import System.Info

import Data.Basic
import Data.Code
import Data.Constraint
import Data.LLVM
import Data.Term
import Data.Tree
import Data.WeakTerm

import qualified Data.HashMap.Strict as Map
import qualified Data.PQueue.Min as Q
import qualified Data.Set as S
import qualified Text.Show.Pretty as Pr

type ConstraintQueue = Q.MinQueue EnrichedConstraint

type IncludeGraph = Map.HashMap (Path Abs File) [Path Abs File]

data Env =
  Env
    { count :: Int -- to generate fresh symbols
    , target :: Maybe Target
    , mainFilePath :: Path Abs File
    , currentFilePath :: Path Abs File
    , includeGraph :: IncludeGraph -- to detect cyclic `include`
    , keywordEnv :: S.Set Identifier -- list of reserved keywords
    , notationEnv :: [(TreePlus, TreePlus)] -- macro transformers
    , constantEnv :: S.Set Identifier
    , defEnv :: Map.HashMap (Path Abs File) [(Meta, Identifier, WeakTermPlus)] -- path ~> identifiers defined in the file at toplevel
    , enumEnv :: Map.HashMap Identifier [Identifier] -- [("choice", ["left", "right"]), ...]
    , revEnumEnv :: Map.HashMap Identifier Identifier -- [("left", "choice"), ("right", "choice"), ...]
    , nameEnv :: Map.HashMap Identifier Identifier -- [("foo", "foo.13"), ...]
    , weakTypeEnv :: Map.HashMap Identifier WeakTermPlus -- var ~> typeof(var)
    , typeEnv :: Map.HashMap Identifier TermPlus
    , constraintEnv :: [PreConstraint] -- for type inference
    , constraintQueue :: ConstraintQueue
    , substEnv :: Map.HashMap Identifier ([Identifier], WeakTermPlus) -- metavar ~> [(metavar in the term, beta-equivalent weakterm)]
    , chainEnv :: Map.HashMap Identifier [(Identifier, TermPlus)] -- var/const ~> the closed var chain of its type
    , codeEnv :: Map.HashMap Identifier ([Identifier], CodePlus) -- f ~> thunk (lam (x1 ... xn) e)
    , llvmEnv :: Map.HashMap Identifier ([Identifier], LLVM)
    }

initialEnv :: Path Abs File -> Env
initialEnv path =
  Env
    { count = 0
    , target = Nothing
    , includeGraph = Map.empty
    , notationEnv = []
    , keywordEnv = S.empty
    , constantEnv = S.empty
    , enumEnv = Map.empty
    , defEnv = Map.empty
    , revEnumEnv = Map.empty
    , nameEnv = Map.empty
    , weakTypeEnv = Map.empty
    , typeEnv = Map.empty
    , chainEnv = Map.empty
    , codeEnv = Map.empty
    , llvmEnv = Map.empty
    , constraintEnv = []
    , constraintQueue = Q.empty
    , substEnv = Map.empty
    , mainFilePath = path
    , currentFilePath = path
    }

type WithEnv a = StateT Env (ExceptT String IO) a

evalWithEnv :: (Show a) => WithEnv a -> Env -> IO (Either String a)
evalWithEnv c env = do
  resultOrErr <- runExceptT (runStateT c env)
  case resultOrErr of
    Left err -> return $ Left err
    Right (result, _) -> return $ Right result

newName :: WithEnv Identifier
newName = do
  env <- get
  let i = count env
  modify (\e -> e {count = i + 1})
  return $ "-" ++ show i

newNameWith :: Identifier -> WithEnv Identifier
newNameWith s = do
  i <- newName
  let s' = s ++ i -- for debug build (slow)
  -- let s' = "name" ++ i
  modify (\e -> e {nameEnv = Map.insert s s' (nameEnv e)})
  return s'

newLLVMNameWith :: Identifier -> WithEnv Identifier
newLLVMNameWith s = do
  i <- newName
  let s' = llvmString s ++ i -- for debug build (slow)
  -- let s' = "name" ++ i
  modify (\e -> e {nameEnv = Map.insert s s' (nameEnv e)})
  return s'

llvmString :: String -> String
llvmString [] = error "llvmString called for the empty string"
llvmString (c:cs) = llvmHeadChar c : map llvmTailChar cs

foo :: String
foo = "-$._" ++ ['a' .. 'z'] ++ ['A' .. 'Z']

bar :: String
bar = "-$._" ++ ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9']

llvmHeadChar :: Char -> Char
llvmHeadChar c
  | c `elem` foo = c
llvmHeadChar _ = '-'

llvmTailChar :: Char -> Char
llvmTailChar c
  | c `elem` bar = c
llvmTailChar _ = '-'

lookupTypeEnv :: String -> WithEnv TermPlus
lookupTypeEnv s
  | Just i <- asEnumNatNumConstant s = do
    return
      ( emptyMeta
      , TermPiElim
          (emptyMeta, TermConst "is-enum")
          [(emptyMeta, TermEnum $ EnumTypeNatNum i)])
  | Just _ <- asLowTypeMaybe s = return univTerm
  | otherwise = do
    mt <- gets (Map.lookup s . typeEnv)
    case mt of
      Just t -> return t
      Nothing -> throwError $ s ++ " is not found in the type environment."

lookupNameEnv :: String -> WithEnv String
lookupNameEnv s = do
  env <- get
  case Map.lookup s (nameEnv env) of
    Just s' -> return s'
    Nothing -> throwError $ "undefined variable: " ++ show s

isDefinedEnum :: Identifier -> WithEnv Bool
isDefinedEnum name = do
  env <- get
  let labelList = join $ Map.elems $ enumEnv env
  return $ name `elem` labelList

getTarget :: WithEnv Target
getTarget = do
  mtarget <- gets target
  case mtarget of
    Just t -> return t
    Nothing -> do
      currentOS <- getOS
      currentArch <- getArch
      return (currentOS, currentArch)

getOS :: WithEnv OS
getOS = do
  case os of
    "linux" -> return OSLinux
    "darwin" -> return OSDarwin
    s -> throwError $ "unsupported target os: " ++ show s

getArch :: WithEnv Arch
getArch = do
  case arch of
    "x86_64" -> return Arch64
    s -> throwError $ "unsupported target arch: " ++ show s

-- for debug
p :: String -> WithEnv ()
p s = liftIO $ putStrLn s

p' :: (Show a) => a -> WithEnv ()
p' s = liftIO $ putStrLn $ Pr.ppShow s

toStr :: (Show a) => a -> String
toStr s = Pr.ppShow s

toInfo :: (Show a) => String -> a -> String
toInfo s x = "assertion failure:\n" ++ s ++ "\n" ++ toStr x

newDataUpsilonWith :: Identifier -> WithEnv (Identifier, DataPlus)
newDataUpsilonWith name = newDataUpsilonWith' name emptyMeta

newDataUpsilonWith' :: Identifier -> Meta -> WithEnv (Identifier, DataPlus)
newDataUpsilonWith' name m = do
  x <- newNameWith name
  return (x, (m, DataUpsilon x))
