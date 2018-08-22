{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

module Data where

import           Control.Comonad
import           Control.Comonad.Cofree

import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Text.Show.Deriving

import           Data.Functor.Classes

import           System.IO.Unsafe

import           Data.IORef
import           Data.List

import qualified Text.Show.Pretty           as Pr

type Identifier = String

newtype Meta = Meta
  { ident :: Identifier
  } deriving (Show, Eq)

type Level = Int

-- S-expression
-- the "F" stands for "Functor"
data TreeF a
  = TreeAtom Identifier
  | TreeNode [a]

deriving instance Show a => Show (TreeF a)

deriving instance Functor TreeF

$(deriveShow1 ''TreeF)

type Tree = Cofree TreeF Identifier

recurM :: (Monad m) => (Tree -> m Tree) -> Tree -> m Tree
recurM f (meta :< TreeAtom s) = f (meta :< TreeAtom s)
recurM f (meta :< TreeNode tis) = do
  tis' <- mapM (recurM f) tis
  f (meta :< TreeNode tis')

-- (undetermined) level of universe
data WeakLevel
  = WeakLevelFixed Int
  | WeakLevelHole Identifier
  deriving (Show, Eq)

data ArgF a
  = ArgIdent Identifier
  | ArgLift a
  | ArgColift a
  | ArgHole Identifier
  deriving (Show)

$(deriveShow1 ''ArgF)

type Arg = Cofree ArgF Identifier

data TypeF a
  = TypeVar Identifier
  | TypeForall (Arg, a)
               a
  | TypeNode Identifier
             [a]
  | TypeUp a
  | TypeDown a
  | TypeUniv WeakLevel
  | TypeHole Identifier

deriving instance Show a => Show (TypeF a)

deriving instance Functor TypeF

$(deriveShow1 ''TypeF)

data Fix f =
  Fix (f (Fix f))

instance Show1 f => Show (Fix f) where
  showsPrec d (Fix a) =
    showParen (d >= 11) $ showString "Fix " . showsPrec1 11 a

-- type Type = Cofree TypeF Identifier
type Type = Fix TypeF

type Region = Identifier

type RegionType = Cofree TypeF Region

data PatF a
  = PatHole
  | PatVar Identifier
  | PatApp Identifier
           [a]
  deriving (Show, Eq)

$(deriveShow1 ''PatF)

deriving instance Functor PatF

type Pat = Cofree PatF Identifier

type Occurrence = [Int]

data Decision a
  = DecisionLeaf [(Occurrence, Identifier)]
                 a
  | DecisionSwitch Occurrence
                   [((Identifier, Int), Decision a)] -- [((constructor, id), cont)]
                   (Maybe (Maybe Identifier, Decision a))
  | DecisionSwap Int
                 (Decision a)
  deriving (Show)

deriving instance Functor Decision

$(deriveShow1 ''Decision)

data TermF a
  = TermVar Identifier
  | TermLam Arg
            a -- positive or negative
  | TermApp a
            a
  | TermLift a
  | TermColift a
  | TermThunk a
  | TermUnthunk a
  | TermMu Arg
           a
  | TermCase [a]
             [([Pat], a)]
  | TermDecision [a]
                 (Decision a)

$(deriveShow1 ''TermF)

type Term = Cofree TermF Identifier

data Polarity
  = PolarityHole Identifier
  | PolarityPositive
  | PolarityNegative
  deriving (Show)

instance (Show a) => Show (IORef a) where
  show a = show (unsafePerformIO (readIORef a))

type ValueInfo = (Identifier, [(Identifier, Type)], Type)

type Index = [Int]

forallArgs :: Type -> (Type, [(Arg, Type)])
forallArgs (Fix (TypeForall (i, vt) t)) = do
  let (body, xs) = forallArgs t
  (body, (i, vt) : xs)
forallArgs body = (body, [])

data Data
  = DataPointer Identifier -- var is something that points already-allocated data
  | DataCell Identifier -- value of defined data types
             Int -- nth constructor
             [Data]
  | DataLabel Identifier -- the address of quoted code
  | DataElemAtIndex Identifier -- subvalue of an inductive value
                    Index
  | DataInt32 Int
  deriving (Show)

type Branch = (Identifier, Int, Identifier)

type Address = Identifier

type DefaultBranch = Identifier

data Code
  = CodeReturn Data
  | CodeLet Identifier -- bind (we also use this to represent application)
            Data
            Code
  | CodeSwitch Identifier -- branching in pattern-matching (elimination of inductive type)
               DefaultBranch
               [Branch]
  | CodeJump Identifier -- unthunk (the target label of the jump address)
  | CodeIndirectJump Identifier -- the name of register
                     Identifier -- the id of corresponding unthunk
                     [Identifier] -- possible jump
  | CodeRecursiveJump Identifier -- jump by (unthunk x) in (mu x (...))
  | CodeCall Identifier -- the register that stores the result of a function call
             Identifier -- the name of the function
             [(Identifier, Data)] -- arguments
             Code
  | CodeWithArg [(Identifier, Data)]
                Code
  deriving (Show)

letSeq :: [Identifier] -> [Data] -> Code -> WithEnv Code
letSeq [] [] code = return code
letSeq (i:is) (d:ds) code = do
  tmp <- letSeq is ds code
  return $ CodeLet i d tmp
letSeq _ _ _ = error "Virtual.letSeq: invalid arguments"

data AsmData
  = AsmDataRegister Identifier
  | AsmDataLabel Identifier
  | AsmDataInt Int
  deriving (Show)

data Asm
  = AsmReturn (Identifier, Type)
  | AsmLet Identifier
           AsmOperation
  | AsmStore Type -- the type of source
             AsmData -- source data
             Identifier -- destination register
  | AsmBranch Identifier
  | AsmIndirectBranch Identifier
                      [Identifier]
  | AsmSwitch Identifier
              DefaultBranch
              [(Identifier, Int, Identifier)]
  deriving (Show)

data AsmOperation
  = AsmAlloc Type
  | AsmLoad Type -- the type of source register
            Identifier -- source register
  | AsmGetElemPointer Type -- the type of base register
                      Identifier -- base register
                      Index -- index
  | AsmCall (Identifier, Type)
            [(Identifier, Type)]
  | AsmBitcast Type
               Identifier
               Type
  deriving (Show)

data Env = Env
  { count            :: Int -- to generate fresh symbols
  , valueEnv         :: [ValueInfo] -- defined values
  , constructorEnv   :: [(Identifier, IORef [Identifier])]
  , notationEnv      :: [(Tree, Tree)] -- macro transformers
  , reservedEnv      :: [Identifier] -- list of reserved keywords
  , nameEnv          :: [(Identifier, Identifier)] -- used in alpha conversion
  , typeEnv          :: [(Identifier, Type)] -- polarized type environment
  , polEnv           :: [(Identifier, Polarity)]
  , constraintEnv    :: [(Type, Type)] -- used in type inference
  , polConstraintEnv :: [(Polarity, Polarity)]
  , argConstraintEnv :: [(Arg, Arg)]
  , levelEnv         :: [(WeakLevel, WeakLevel)] -- constraint regarding the level of universes
  , codeEnv          :: [(Identifier, IORef [(Identifier, IORef Code)])]
  , didUpdate        :: Bool -- used in live analysis to detect the end of the process
  , scope            :: Identifier -- used in Virtual to determine the name of current function
  } deriving (Show)

initialEnv :: Env
initialEnv =
  Env
    { count = 0
    , valueEnv = []
    , constructorEnv = []
    , notationEnv = []
    , reservedEnv =
        [ "thunk"
        , "lambda"
        , "return"
        , "bind"
        , "unthunk"
        , "mu"
        , "case"
        , "ascribe"
        , "down"
        , "universe"
        , "forall"
        , "up"
        ]
    , nameEnv = []
    , typeEnv = []
    , polEnv = []
    , constraintEnv = []
    , polConstraintEnv = []
    , argConstraintEnv = []
    , levelEnv = []
    , codeEnv = []
    , didUpdate = False
    , scope = ""
    }

type WithEnv a = StateT Env (ExceptT String IO) a

runWithEnv :: WithEnv a -> Env -> IO (Either String (a, Env))
runWithEnv c env = runExceptT (runStateT c env)

evalWithEnv :: (Show a) => WithEnv a -> Env -> IO ()
evalWithEnv c env = do
  x <- runWithEnv c env
  case x of
    Left err -> putStrLn err
    Right (y, env) -> do
      putStrLn $ Pr.ppShow y
      putStrLn $ Pr.ppShow env

newName :: WithEnv Identifier
newName = do
  env <- get
  let i = count env
  modify (\e -> e {count = i + 1})
  return $ "." ++ show i

newNameWith :: Identifier -> WithEnv Identifier
newNameWith s = do
  i <- newName
  let s' = s ++ i
  modify (\e -> e {nameEnv = (s, s') : nameEnv e})
  return s'

lookupTypeEnv :: String -> WithEnv (Maybe Type)
lookupTypeEnv s = gets (lookup s . typeEnv)

lookupTypeEnv' :: String -> WithEnv Type
lookupTypeEnv' s = do
  mt <- gets (lookup s . typeEnv)
  case mt of
    Nothing -> lift $ throwE $ s ++ " is not found in the type environment"
    Just t  -> return t

lookupPolEnv :: String -> WithEnv (Maybe Polarity)
lookupPolEnv s = gets (lookup s . polEnv)

lookupPolEnv' :: String -> WithEnv Polarity
lookupPolEnv' s = do
  mpol <- gets (lookup s . polEnv)
  case mpol of
    Nothing  -> lift $ throwE $ s ++ " is not found in the type environment"
    Just pol -> return pol

lookupVEnv :: String -> WithEnv (Maybe ValueInfo)
lookupVEnv s = do
  env <- get
  return $ find (\(x, _, _) -> x == s) $ valueEnv env

lookupVEnv' :: String -> WithEnv ValueInfo
lookupVEnv' s = do
  mt <- lookupVEnv s
  case mt of
    Just t -> return t
    Nothing -> do
      lift $ throwE $ "the value " ++ show s ++ " is not defined "

lookupNameEnv :: String -> WithEnv String
lookupNameEnv s = do
  env <- get
  case lookup s (nameEnv env) of
    Just s' -> return s'
    Nothing -> lift $ throwE $ "undefined variable: " ++ show s

lookupNameEnv' :: String -> WithEnv String
lookupNameEnv' s = do
  env <- get
  case lookup s (nameEnv env) of
    Just s' -> return s'
    Nothing -> newNameWith s

lookupCodeEnv :: Identifier -> WithEnv (IORef [(Identifier, IORef Code)])
lookupCodeEnv scope = do
  m <- gets (lookup scope . codeEnv)
  case m of
    Nothing     -> lift $ throwE $ "no such scope: " ++ show scope
    Just envRef -> return envRef

lookupCurrentCodeEnv :: WithEnv (IORef [(Identifier, IORef Code)])
lookupCurrentCodeEnv = do
  scope <- getScope
  lookupCodeEnv scope

lookupCodeEnv2 :: Identifier -> Identifier -> WithEnv (IORef Code)
lookupCodeEnv2 scope ident = do
  scopeEnvRef <- lookupCodeEnv scope
  scopeEnv <- liftIO $ readIORef scopeEnvRef
  case lookup ident scopeEnv of
    Just codeRef -> return codeRef
    Nothing ->
      lift $
      throwE $ "no such label " ++ show ident ++ " defined in scope " ++ scope

insTypeEnv :: Identifier -> Type -> WithEnv ()
insTypeEnv i t = modify (\e -> e {typeEnv = (i, t) : typeEnv e})

insPolEnv :: Identifier -> Polarity -> WithEnv ()
insPolEnv i pol = modify (\e -> e {polEnv = (i, pol) : polEnv e})

insCodeEnv :: Identifier -> Identifier -> IORef Code -> WithEnv ()
insCodeEnv scope ident codeRef = do
  scopeEnvRef <- lookupCodeEnv scope
  scopeEnv <- liftIO $ readIORef scopeEnvRef
  liftIO $ writeIORef scopeEnvRef ((ident, codeRef) : scopeEnv)

insCurrentCodeEnv :: Identifier -> IORef Code -> WithEnv ()
insCurrentCodeEnv ident codeRef = do
  scope <- getScope
  insCodeEnv scope ident codeRef

updateCodeEnv :: Identifier -> Identifier -> Code -> WithEnv ()
updateCodeEnv scope label code = do
  codeRef <- lookupCodeEnv2 scope label
  liftIO $ writeIORef codeRef code

updateCurrentCodeEnv :: Identifier -> Code -> WithEnv ()
updateCurrentCodeEnv ident code = do
  scope <- getScope
  updateCodeEnv scope ident code

insEmptyCodeEnv :: Identifier -> WithEnv ()
insEmptyCodeEnv scope = do
  nop <- liftIO $ newIORef []
  modify (\e -> e {codeEnv = (scope, nop) : codeEnv e})

lookupConstructorEnv :: Identifier -> WithEnv [Identifier]
lookupConstructorEnv cons = do
  env <- get
  case lookup cons (constructorEnv env) of
    Nothing -> lift $ throwE $ "no such constructor defined: " ++ show cons
    Just cenvRef -> liftIO $ readIORef cenvRef

getConstructorNumber :: Identifier -> Identifier -> WithEnv Int
getConstructorNumber nodeName ident = do
  env <- get
  case lookup nodeName (constructorEnv env) of
    Nothing -> lift $ throwE $ "no such type defined: " ++ show nodeName
    Just cenvRef -> do
      cenv <- liftIO $ readIORef cenvRef
      case elemIndex ident cenv of
        Nothing -> lift $ throwE $ "no such constructor defined: " ++ ident
        Just i  -> return i

insConstraintEnv :: Type -> Type -> WithEnv ()
insConstraintEnv t1 t2 =
  modify (\e -> e {constraintEnv = (t1, t2) : constraintEnv e})

insPolConstraintEnv :: Polarity -> Polarity -> WithEnv ()
insPolConstraintEnv pol1 pol2 =
  modify (\e -> e {polConstraintEnv = (pol1, pol2) : polConstraintEnv e})

insArgConstraintEnv :: Arg -> Arg -> WithEnv ()
insArgConstraintEnv arg1 arg2 =
  modify (\e -> e {argConstraintEnv = (arg1, arg2) : argConstraintEnv e})

insLEnv :: WeakLevel -> WeakLevel -> WithEnv ()
insLEnv l1 l2 = modify (\e -> e {levelEnv = (l1, l2) : levelEnv e})

insConstructorEnv :: Identifier -> Identifier -> WithEnv ()
insConstructorEnv i cons = do
  env <- get
  case lookup i (constructorEnv env) of
    Nothing -> do
      cenvRef <- liftIO $ newIORef [cons]
      modify (\e -> e {constructorEnv = (i, cenvRef) : constructorEnv env})
    Just cenvRef -> do
      cenv <- liftIO $ readIORef cenvRef
      liftIO $ writeIORef cenvRef (cons : cenv)

setScope :: Identifier -> WithEnv ()
setScope i = do
  modify (\e -> e {scope = i})

getScope :: WithEnv Identifier
getScope = do
  env <- get
  return $ scope env

local :: WithEnv a -> WithEnv a
local p = do
  env <- get
  x <- p
  modify (\e -> env {count = count e})
  return x

foldMTermL ::
     (Cofree f Identifier -> a -> f (Cofree f Identifier))
  -> Cofree f Identifier
  -> [a]
  -> StateT Env (ExceptT String IO) (Cofree f Identifier)
foldMTermL _ e [] = return e
foldMTermL f e (t:ts) = do
  let tmp = f e t
  i <- newName
  foldMTermL f (i :< tmp) ts

foldMTermR ::
     (a -> Cofree f Identifier -> f (Cofree f Identifier))
  -> Cofree f Identifier
  -> [a]
  -> StateT Env (ExceptT String IO) (Cofree f Identifier)
foldMTermR _ e [] = return e
foldMTermR f e (t:ts) = do
  tmp <- foldMTermR f e ts
  let x = f t tmp
  i <- newName
  return $ i :< x

foldMTermR' ::
     (a -> Fix f -> f (Fix f))
  -> Fix f
  -> [a]
  -> StateT Env (ExceptT String IO) (Fix f)
foldMTermR' _ e [] = return e
foldMTermR' f e (t:ts) = do
  tmp <- foldMTermR' f e ts
  let x = f t tmp
  return $ Fix x

swap :: Int -> Int -> [a] -> [a]
swap i j xs = do
  replaceNth j (xs !! i) (replaceNth i (xs !! j) xs)

replaceNth :: Int -> a -> [a] -> [a]
replaceNth _ _ [] = []
replaceNth n newVal (x:xs)
  | n == 0 = newVal : xs
  | otherwise = x : replaceNth (n - 1) newVal xs
