{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

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
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Text.Show.Pretty as Pr

type ConstraintQueue = Q.MinQueue EnrichedConstraint

type IncludeGraph = Map.HashMap (Path Abs File) [Path Abs File]

type FileInfo = [(Meta, Identifier, WeakTermPlus)]

type FileEnv = Map.HashMap (Path Abs File) FileInfo

type Justification = Loc

type RuleEnv = Map.HashMap Identifier (Maybe [Data.WeakTerm.IdentifierPlus])

data Env =
  Env
    { count :: Integer -- to generate fresh symbols
    , phase :: Integer
    , target :: Maybe Target
    , mainFilePath :: Path Abs File
    , currentFilePath :: Path Abs File
    , includeGraph :: IncludeGraph -- to detect cyclic `include`
    , keywordEnv :: S.Set Identifier -- list of reserved keywords
    , notationEnv :: [(TreePlus, TreePlus)] -- macro transformers
    , constantEnv :: S.Set Identifier
    , fileEnv :: FileEnv -- path ~> identifiers defined in the file at toplevel
    , enumEnv :: Map.HashMap Identifier [(Identifier, Int)] -- [("choice", [("left", 0), ("right", 1)]), ...]
    , revEnumEnv :: Map.HashMap Identifier (Identifier, Int) -- [("left", ("choice", 0)), ("right", ("choice", 1)), ...]
    , nameEnv :: Map.HashMap Identifier Identifier -- [("foo", "foo.13"), ...]
    , revNameEnv :: Map.HashMap Identifier Identifier -- [("foo.13", "foo"), ...]
    , formationEnv :: Map.HashMap Identifier (Maybe WeakTermPlus)
    , inductiveEnv :: RuleEnv -- "list" ~> (cons, Pi (A : tau). A -> list A -> list A)
    , coinductiveEnv :: RuleEnv -- "tail" ~> (head, Pi (A : tau). stream A -> A)
    , weakTypeEnv :: Map.HashMap Identifier WeakTermPlus -- var ~> typeof(var)
    , typeEnv :: Map.HashMap Identifier TermPlus
    , constraintEnv :: [PreConstraint] -- for type inference
    , constraintQueue :: ConstraintQueue
    , levelEnv :: [LevelConstraint]
    , substEnv :: Map.HashMap Identifier WeakTermPlus -- metavar ~> beta-equivalent weakterm
    , zetaEnv :: Map.HashMap Identifier (WeakTermPlus, WeakTermPlus)
    , chainEnv :: Map.HashMap Identifier [(Meta, Identifier, TermPlus)] -- var/const ~> the closed var chain of its type
    , codeEnv :: Map.HashMap Identifier ([Identifier], CodePlus) -- f ~> thunk (lam (x1 ... xn) e)
    , llvmEnv :: Map.HashMap Identifier ([Identifier], LLVM)
    , shouldColorize :: Bool
    }

initialEnv :: Path Abs File -> Bool -> Env
initialEnv path colorizeFlag =
  Env
    { count = 0
    , phase = 0
    , target = Nothing
    , includeGraph = Map.empty
    , notationEnv = []
    , keywordEnv = S.empty
    , constantEnv = S.empty
    , enumEnv = Map.empty
    , fileEnv = Map.empty
    , revEnumEnv = Map.empty
    , nameEnv = Map.empty
    , revNameEnv = Map.empty
    , formationEnv = Map.empty
    , inductiveEnv = Map.empty
    , coinductiveEnv = Map.empty
    , weakTypeEnv = Map.empty
    , typeEnv = Map.empty
    , chainEnv = Map.empty
    , codeEnv = Map.empty
    , llvmEnv = Map.empty
    , constraintEnv = []
    , constraintQueue = Q.empty
    , levelEnv = []
    , substEnv = Map.empty
    , zetaEnv = Map.empty
    , mainFilePath = path
    , currentFilePath = path
    , shouldColorize = colorizeFlag
    }

-- type WithEnv a = StateT Env (ExceptT Identifier IO) a
type WithEnv a = StateT Env (ExceptT [IO ()] IO) a

evalWithEnv :: (Show a) => WithEnv a -> Env -> IO (Either [IO ()] a)
evalWithEnv c env = do
  resultOrErr <- runExceptT (runStateT c env)
  case resultOrErr of
    Left err -> return $ Left err
    Right (result, _) -> return $ Right result

throwError' :: Identifier -> WithEnv a
throwError' x = throwError [TIO.putStrLn x]

addErrorAction :: IO () -> WithEnv a -> WithEnv a
addErrorAction action computation = do
  catchError computation $ \err -> throwError $ action : err

-- evalWithEnv :: (Show a) => WithEnv a -> Env -> IO (Either String a)
-- evalWithEnv c env = do
--   resultOrErr <- runExceptT (runStateT c env)
--   case resultOrErr of
--     Left err -> return $ Left $ T.unpack err
--     Right (result, _) -> return $ Right result
newCount :: WithEnv Integer
newCount = do
  i <- gets count
  -- let i = count env
  modify (\e -> e {count = i + 1})
  return i

newUnivLevel :: WithEnv UnivLevel
newUnivLevel = newCount

newName :: WithEnv Identifier
newName = do
  i <- newCount
  return $ "-" <> T.pack (show i)

newNameWith :: Identifier -> WithEnv Identifier
newNameWith s = do
  i <- newName
  let s' = s <> i -- slow
  -- let s' = i
  modify (\e -> e {nameEnv = Map.insert s s' (nameEnv e)})
  -- modify (\e -> e {revNameEnv = Map.insert s' s (revNameEnv e)})
  return s'

newLLVMNameWith :: Identifier -> WithEnv Identifier
newLLVMNameWith s = do
  i <- newName
  let s' = llvmString s <> i
  modify (\e -> e {nameEnv = Map.insert s' s (nameEnv e)})
  modify (\e -> e {revNameEnv = Map.insert s' s (revNameEnv e)})
  return s'

llvmString :: Identifier -> Identifier
llvmString "" = error "llvmString called for the empty string"
llvmString s = T.cons (llvmHeadChar $ T.head s) (T.map llvmTailChar $ T.tail s)

llvmHeadCharSet :: S.Set Char
llvmHeadCharSet =
  S.fromList $
  "-$._" <> "abcdefghijklmnopqrstuvwxyz" <> "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

llvmHeadChar :: Char -> Char
llvmHeadChar x =
  if x `S.member` llvmHeadCharSet
    then x
    else '-'

llvmTailCharSet :: S.Set Char
llvmTailCharSet =
  S.fromList $
  "-$._" <>
  "abcdefghijklmnopqrstuvwxyz" <> "ABCDEFGHIJKLMNOPQRSTUVWXYZ" <> "0123456789"

-- foo = S.fromList $ "-$._" <> "abcdefghijklmnopqrstuvwxyz" <> "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
llvmTailChar :: Char -> Char
llvmTailChar x =
  if x `S.member` llvmTailCharSet
    then x
    else '-'

lookupTypeEnv :: Identifier -> WithEnv TermPlus
lookupTypeEnv s
  | Just i <- asEnumNatConstant s = do
    return
      ( emptyMeta
      , TermPiElim
          (emptyMeta, TermConst "is-enum")
          [(emptyMeta, TermEnum $ EnumTypeNat i)])
  | Just _ <- asLowTypeMaybe s = return univTerm
  | otherwise = do
    mt <- gets (Map.lookup s . typeEnv)
    case mt of
      Just t -> return t
      Nothing ->
        throwError
          [TIO.putStrLn $ s <> " is not found in the type environment."]

lookupNameEnv :: Identifier -> WithEnv Identifier
lookupNameEnv s = do
  env <- get
  case Map.lookup s (nameEnv env) of
    Just s' -> return s'
    Nothing -> throwError [TIO.putStrLn $ "undefined variable: " <> s]

isDefinedEnum :: Identifier -> WithEnv Bool
isDefinedEnum name = do
  env <- get
  let labelList = join $ Map.elems $ enumEnv env
  return $ name `elem` map fst labelList

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
    s -> throwError [putStrLn $ "unsupported target os: " <> show s]

getArch :: WithEnv Arch
getArch = do
  case arch of
    "x86_64" -> return Arch64
    s ->
      throwError [TIO.putStrLn $ "unsupported target arch: " <> T.pack (show s)]

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

enumValueToInteger :: EnumValue -> WithEnv Integer
enumValueToInteger labelOrNat =
  case labelOrNat of
    EnumValueLabel l -> toInteger <$> getEnumNum l
    EnumValueIntS _ i -> return i
    EnumValueIntU _ i -> return i
    EnumValueNat _ j -> return j

getEnumNum :: Identifier -> WithEnv Int
getEnumNum label
  -- ienv <- gets enumEnv
 = do
  renv <- gets revEnumEnv
  case Map.lookup label renv of
    Nothing -> throwError [TIO.putStrLn $ "no such enum is defined: " <> label]
    Just (_, i) -> return i
  -- case (getEnumNum' label $ Map.elems ienv) of
  --   Nothing -> throwError [TIO.putStrLn $ "no such enum is defined: " <> label]
  --   Just i -> return i

-- getEnumNum' :: Identifier -> [[Identifier]] -> Maybe Int
-- getEnumNum' _ [] = Nothing
-- getEnumNum' l (xs:xss) =
--   case elemIndex l xs of
--     Nothing -> getEnumNum' l xss
--     Just i -> Just i
-- {enum.top, enum.choice, etc.} ~> {(the number of contents in enum)}
-- enum.n{i}とかも処理できないとだめ。
-- これ、enumNatNumのやつを後ろにしてたってことは、enum.n8とかがNothingになってたってこと？
asEnumConstant :: Identifier -> WithEnv (Maybe Integer)
asEnumConstant x
  | ["enum", y] <- wordsBy '.' x = do
    eenv <- gets enumEnv
    case Map.lookup y eenv of
      Nothing -> return Nothing
      Just ls -> return $ Just $ toInteger $ length ls
  | Just i <- asEnumNatConstant x = return $ Just i
asEnumConstant _ = return Nothing

pp :: WeakTermPlus -> WithEnv ()
pp e = liftIO $ TIO.putStrLn $ toText e
