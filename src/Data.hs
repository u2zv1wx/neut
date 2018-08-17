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

-- import           Data.Functor.Foldable
import qualified Text.Show.Pretty           as Pr

type Identifier = String

newtype Meta = Meta
  { ident :: Identifier
  } deriving (Show, Eq)

-- (undetermined) level of universe
data WeakLevel
  = WeakLevelFixed Int
  | WeakLevelHole Identifier
  deriving (Show, Eq)

type Level = Int

-- S-expression
-- the "F" stands for "Functor"
data TreeF a
  = TreeAtom Identifier
  | TreeNode [a]

deriving instance Show a => Show (TreeF a)

deriving instance Functor TreeF

$(deriveShow1 ''TreeF)

type Tree = Cofree TreeF Meta

recurM :: (Monad m) => (Tree -> m Tree) -> Tree -> m Tree
recurM f (meta :< TreeAtom s) = f (meta :< TreeAtom s)
recurM f (meta :< TreeNode tis) = do
  tis' <- mapM (recurM f) tis
  f (meta :< TreeNode tis')

data IdentOrHole
  = Ident Identifier
  | Hole Identifier
  deriving (Show, Eq)

-- weaktype
-- WT ::= P | N
data WeakType
  = WeakTypeVar Identifier
  | WeakTypePosHole Identifier
  | WeakTypeNegHole Identifier
  | WeakTypeNode Identifier
                 [WeakType]
  | WeakTypeUp WeakType
  | WeakTypeDown WeakType
                 Identifier
  | WeakTypeUniv WeakLevel
  | WeakTypeForall (IdentOrHole, WeakType)
                   WeakType
  deriving (Show, Eq)

-- value type
-- P ::= p
--     | (down N)
--     | {defined constant type}
--     | (node (x P) P)
--     | (p p)
--     | (universe i)
data ValueType
  = ValueTypeVar Identifier
  | ValueTypeNode Identifier
                  [ValueType]
  | ValueTypeDown CompType
  | ValueTypeUniv Level
  deriving (Show, Eq)

-- computation type
-- N ::= (forall (x P) N)
--     | (up P)
data CompType
  = CompTypeForall (Identifier, ValueType)
                   CompType
  | CompTypeUp ValueType
  deriving (Show, Eq)

data Type
  = TypeValueType ValueType
  | TypeCompType CompType
  deriving (Show)

weakenValueType :: ValueType -> WeakType
weakenValueType (ValueTypeVar i) = WeakTypeVar i
weakenValueType (ValueTypeNode s ts) = do
  let ts' = map weakenValueType ts
  WeakTypeNode s ts'
weakenValueType (ValueTypeDown c) = WeakTypeDown (weakenCompType c) "ANY"
weakenValueType (ValueTypeUniv l) = WeakTypeUniv (WeakLevelFixed l)

weakenCompType :: CompType -> WeakType
weakenCompType (CompTypeForall (i, t1) t2) = do
  let t1' = weakenValueType t1
  let t2' = weakenCompType t2
  WeakTypeForall (Ident i, t1') t2'
weakenCompType (CompTypeUp v) = WeakTypeUp (weakenValueType v)

data PatF a
  = PatHole
  | PatVar Identifier
  | PatApp Identifier
           [a]
  deriving (Show, Eq)

$(deriveShow1 ''PatF)

deriving instance Functor PatF

type Pat = Cofree PatF Meta

type Occurrence = ([Int], ValueType)

data Decision a
  = DecisionLeaf [(Occurrence, (Identifier, ValueType))]
                 a
  | DecisionSwitch Occurrence
                   [((Identifier, Int), Decision a)]
                   (Maybe (Maybe Identifier, Decision a))
  | DecisionSwap Int
                 (Decision a)
  deriving (Show)

deriving instance Functor Decision

$(deriveShow1 ''Decision)

-- value / positive term
-- v ::= x
--     | {defined constant} <- nat, succ, etc.
--     | (v v)
--     | (thunk e)
data ValueF c v
  = ValueVar Identifier
  | ValueNodeApp Identifier
                 [v]
  | ValueThunk c
               Identifier
  deriving (Show)

-- computation / negative term
-- e ::= (lambda (x P) e)
--     | (e v)
--     | (return v)
--     | (bind (x P) e1 e2)
--     | (unthunk v)
--     | (mu (x P) e)
--     | (case e (v1 e1) ... (vn en))
data CompF v c
  = CompLam Identifier
            c
  | CompApp c
            v
  | CompRet v
  | CompBind Identifier
             c
             c
  | CompUnthunk v
                Identifier
  | CompMu Identifier
           c
  | CompCase [v]
             (Decision c)
  deriving (Show)

$(deriveShow1 ''ValueF)

$(deriveShow1 ''CompF)

data VMeta = VMeta
  { vtype :: ValueType
  } deriving (Show)

data CMeta = CMeta
  { ctype :: CompType
  } deriving (Show)

type PreValue = Cofree (ValueF Comp) VMeta

type PreComp = Cofree (CompF Value) CMeta

newtype Value =
  Value PreValue
  deriving (Show)

newtype Comp =
  Comp PreComp
  deriving (Show)

data Term
  = TermValue Value
  | TermComp Comp
  deriving (Show)

data WeakTermF a
  = WeakTermVar Identifier
  | WeakTermNodeApp Identifier
                    [a]
  | WeakTermThunk a
  | WeakTermLam Identifier
                a
  | WeakTermApp a
                a
  | WeakTermRet a
  | WeakTermBind Identifier
                 a
                 a
  | WeakTermUnthunk a
  | WeakTermMu Identifier
               a
  | WeakTermCase [a]
                 [([Pat], a)]
  | WeakTermAsc a
                WeakType

$(deriveShow1 ''WeakTermF)

deriving instance Show a => Show (WeakTermF a)

deriving instance Functor WeakTermF

type WeakTerm = Cofree WeakTermF Meta

instance (Show a) => Show (IORef a) where
  show a = show (unsafePerformIO (readIORef a))

type ValueInfo = (Identifier, [(Identifier, ValueType)], ValueType)

type Index = [Int]

data LowType
  = LowTypeNull
  | LowTypeInt8
  | LowTypeInt32
  | LowTypeStruct [LowType]
  | LowTypePointer LowType
  | LowTypeLabel
  deriving (Show)

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

type Function = Identifier

type Label = (Function, Identifier)

type DefaultBranch = Label

data Code
  = CodeReturn Identifier -- return register
               Label -- link label
               Data
  | CodeLet Identifier -- bind (we also use this to represent application)
            Data
            Code
  | CodeLetLink Identifier -- link register
                Data -- address
                Code
  | CodeSwitch Identifier -- branching in pattern-matching (elimination of inductive type)
               DefaultBranch
               [Branch]
  | CodeJump Label -- unthunk (the target label of the jump address)
  | CodeIndirectJump Identifier -- the name of register
                     Identifier -- the id of corresponding unthunk
                     [Identifier] -- possible jump
  | CodeRecursiveJump Label -- jump by (unthunk x) in (mu x (...))
  | CodeCall [(Identifier, Data)]
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
  = AsmLet Identifier
           AsmOperation
  | AsmStore LowType -- the type of source
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
  = AsmAlloc LowType
  | AsmLoad LowType -- the type of source register
            Identifier -- source register
  | AsmGetElemPointer LowType -- the type of base register
                      Identifier -- base register
                      Index -- (semantically sane) index
  | AsmStackSave
  | AsmStackRestore
  deriving (Show)

data Env = Env
  { count          :: Int -- to generate fresh symbols
  , valueEnv       :: [ValueInfo] -- defined values
  , constructorEnv :: [(Identifier, IORef [Identifier])]
  , notationEnv    :: [(Tree, Tree)] -- macro transformers
  , reservedEnv    :: [Identifier] -- list of reserved keywords
  , nameEnv        :: [(Identifier, Identifier)] -- used in alpha conversion
  , weakTypeEnv    :: [(Identifier, WeakType)] -- used in type inference
  , typeEnv        :: [(Identifier, Type)] -- polarized type environment
  , valueTypeEnv   :: [(Identifier, ValueType)]
  , constraintEnv  :: [(WeakType, WeakType)] -- used in type inference
  , levelEnv       :: [(WeakLevel, WeakLevel)] -- constraint regarding the level of universes
  , argEnv         :: [(IdentOrHole, IdentOrHole)] -- equivalence of arguments of forall
  , thunkEnv       :: [(Identifier, Identifier)]
  , codeEnv        :: [(Identifier, IORef [(Identifier, IORef Code)])]
  -- , codeEnv         :: [(Label, IORef Code)]
  , lowTypeEnv     :: [(Identifier, LowType)]
  , didUpdate      :: Bool -- used in live analysis to detect the end of the process
  , linkRegister   :: Maybe Identifier
  , returnRegister :: Maybe Identifier
  , returnAddr     :: [Identifier]
  , scope          :: Identifier -- used in Virtual to determine the name of current function
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
    , weakTypeEnv = []
    , typeEnv = []
    , valueTypeEnv = []
    , constraintEnv = []
    , levelEnv = []
    , thunkEnv = []
    , argEnv = []
    , codeEnv = []
    , lowTypeEnv = []
    , didUpdate = False
    , linkRegister = Nothing
    , returnRegister = Nothing
    , returnAddr = ["exit"]
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

lookupWTEnv :: String -> WithEnv (Maybe WeakType)
lookupWTEnv s = gets (lookup s . weakTypeEnv)

lookupTEnv :: String -> WithEnv (Maybe Type)
lookupTEnv s = gets (lookup s . typeEnv)

lookupWTEnv' :: String -> WithEnv WeakType
lookupWTEnv' s = do
  mt <- lookupWTEnv s
  case mt of
    Just t -> return t
    Nothing -> do
      env <- get
      lift $
        throwE $
        "the type of " ++
        show s ++
        " is not defined in the type environment. typeEnv:\n" ++
        (Pr.ppShow $ weakTypeEnv env)

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
lookupCodeEnv label = do
  m <- gets (lookup label . codeEnv)
  case m of
    Nothing     -> lift $ throwE $ "no such label: " ++ show label
    Just envRef -> return envRef

lookupCodeEnv' :: Identifier -> Identifier -> WithEnv (IORef Code)
lookupCodeEnv' scope ident = do
  scopeEnvRef <- lookupCodeEnv scope
  scopeEnv <- liftIO $ readIORef scopeEnvRef
  case lookup ident scopeEnv of
    Just codeRef -> return codeRef
    Nothing ->
      lift $
      throwE $ "no such label " ++ show ident ++ " defined in scope " ++ scope

insCodeEnv :: Identifier -> Identifier -> IORef Code -> WithEnv ()
insCodeEnv scope ident codeRef = do
  scopeEnvRef <- lookupCodeEnv scope
  scopeEnv <- liftIO $ readIORef scopeEnvRef
  liftIO $ writeIORef scopeEnvRef ((ident, codeRef) : scopeEnv)

insCodeEnv' :: Identifier -> IORef Code -> WithEnv ()
insCodeEnv' ident codeRef = do
  scope <- getScope
  insCodeEnv scope ident codeRef

updateCodeEnv :: Identifier -> Identifier -> Code -> WithEnv ()
updateCodeEnv scope label code = do
  codeRef <- lookupCodeEnv' scope label
  liftIO $ writeIORef codeRef code

updateCodeEnv' :: Identifier -> Code -> WithEnv ()
updateCodeEnv' ident code = do
  scope <- getScope
  updateCodeEnv scope ident code

insEmptyCodeEnv :: Identifier -> WithEnv ()
insEmptyCodeEnv scope = do
  nop <- liftIO $ newIORef []
  modify (\e -> e {codeEnv = (scope, nop) : codeEnv e})

toLabel :: Identifier -> WithEnv Label
toLabel ident = do
  current <- getScope
  return (current, ident)

lookupThunkEnv :: Identifier -> WithEnv [Identifier]
lookupThunkEnv s = do
  env <- get
  let selector pair =
        case pair of
          (x, y)
            | x == s -> [y]
          (x, y)
            | y == s -> [x]
          _ -> []
  return $ concatMap selector $ thunkEnv env

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

insWTEnv :: String -> WeakType -> WithEnv ()
insWTEnv s t = modify (\e -> e {weakTypeEnv = (s, t) : weakTypeEnv e})

insVTEnv :: String -> ValueType -> WithEnv ()
insVTEnv s t = modify (\e -> e {valueTypeEnv = (s, t) : valueTypeEnv e})

insLowTypeEnv :: String -> LowType -> WithEnv ()
insLowTypeEnv s t = modify (\e -> e {lowTypeEnv = (s, t) : lowTypeEnv e})

lookupLowTypeEnv :: String -> WithEnv (Maybe LowType)
lookupLowTypeEnv s = gets (lookup s . lowTypeEnv)

lookupLowTypeEnv' :: String -> WithEnv LowType
lookupLowTypeEnv' s = do
  env <- get
  mt <- lookupLowTypeEnv s
  case mt of
    Just t -> return t
    Nothing -> do
      lift $
        throwE $
        "the type of " ++ show s ++ " is not defined. env: " ++ Pr.ppShow env

lookupValueTypeEnv :: String -> WithEnv (Maybe ValueType)
lookupValueTypeEnv s = gets (lookup s . valueTypeEnv)

lookupValueTypeEnv' :: String -> WithEnv ValueType
lookupValueTypeEnv' s = do
  mt <- lookupValueTypeEnv s
  case mt of
    Just t -> return t
    Nothing -> do
      lift $ throwE $ "the type of " ++ show s ++ " is not defined "

insCEnv :: WeakType -> WeakType -> WithEnv ()
insCEnv t1 t2 = modify (\e -> e {constraintEnv = (t1, t2) : constraintEnv e})

insLEnv :: WeakLevel -> WeakLevel -> WithEnv ()
insLEnv l1 l2 = modify (\e -> e {levelEnv = (l1, l2) : levelEnv e})

insAEnv :: IdentOrHole -> IdentOrHole -> WithEnv ()
insAEnv x y = modify (\e -> e {argEnv = (x, y) : argEnv e})

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

insThunkEnv :: Identifier -> Identifier -> WithEnv ()
insThunkEnv i j = modify (\e -> e {thunkEnv = (i, j) : thunkEnv e})

initializeLinkRegister :: WithEnv ()
initializeLinkRegister = do
  s <- newNameWith "link"
  modify (\e -> e {linkRegister = Just s})

initializeReturnRegister :: WithEnv ()
initializeReturnRegister = do
  s <- newNameWith "ret"
  modify (\e -> e {returnRegister = Just s})

getLinkRegister :: WithEnv Identifier
getLinkRegister = do
  e <- get
  case linkRegister e of
    Just s  -> return s
    Nothing -> lift $ throwE "the name of link register is not defined"

getReturnRegister :: WithEnv Identifier
getReturnRegister = do
  e <- get
  case returnRegister e of
    Just s  -> return s
    Nothing -> lift $ throwE "the name of link register is not defined"

getReturnAddr :: WithEnv Identifier
getReturnAddr = do
  e <- get
  modify (\e -> e {returnAddr = tail (returnAddr e)})
  return $ head $ returnAddr e

setReturnAddr :: Identifier -> WithEnv ()
setReturnAddr addr = do
  modify (\e -> e {returnAddr = addr : returnAddr e})

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

foldMTerm ::
     (Cofree f Meta -> a -> f (Cofree f Meta))
  -> Cofree f Meta
  -> [a]
  -> StateT Env (ExceptT String IO) (Cofree f Meta)
foldMTerm _ e [] = return e
foldMTerm f e (t:ts) = do
  let tmp = f e t
  i <- newName
  foldMTerm f (Meta {ident = i} :< tmp) ts

foldMTermR ::
     (a -> Cofree f Meta -> f (Cofree f Meta))
  -> Cofree f Meta
  -> [a]
  -> StateT Env (ExceptT String IO) (Cofree f Meta)
foldMTermR _ e [] = return e
foldMTermR f e (t:ts) = do
  tmp <- foldMTermR f e ts
  let x = f t tmp
  i <- newName
  return $ Meta {ident = i} :< x
