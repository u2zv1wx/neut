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

import           System.IO.Unsafe

import           Data.IORef

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
  | WeakTypeHole Identifier
  | WeakTypeConst Identifier
  | WeakTypeNode [(Identifier, WeakType)]
                 WeakType
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
  | ValueTypeConst Identifier
  | ValueTypeNode [(Identifier, ValueType)]
                  ValueType
  | ValueTypeDown CompType
                  Identifier
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
weakenValueType (ValueTypeConst i) = WeakTypeConst i
weakenValueType (ValueTypeNode xts t2) = do
  let (xs, ts) = unzip xts
  let ts' = map weakenValueType ts
  let t2' = weakenValueType t2
  WeakTypeNode (zip xs ts') t2'
weakenValueType (ValueTypeDown c i) = WeakTypeDown (weakenCompType c) i
weakenValueType (ValueTypeUniv l) = WeakTypeUniv (WeakLevelFixed l)

weakenCompType :: CompType -> WeakType
weakenCompType (CompTypeForall (i, t1) t2) = do
  let t1' = weakenValueType t1
  let t2' = weakenCompType t2
  WeakTypeForall (Ident i, t1') t2'
weakenCompType (CompTypeUp v) = WeakTypeUp (weakenValueType v)

data PatF a
  = PatVar Identifier
  | PatConst Identifier
  | PatApp Identifier
           [a]
  deriving (Show, Eq)

$(deriveShow1 ''PatF)

deriving instance Functor PatF

type Pat = Cofree PatF Meta

-- value / positive term
-- v ::= x
--     | {defined constant} <- nat, succ, etc.
--     | (v v)
--     | (thunk e)
data ValueF c v
  = ValueVar Identifier
  | ValueConst Identifier
  | ValueNodeApp Identifier
                 [v]
  | ValueThunk c
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
  | CompMu Identifier
           c
  | CompCase v
             [(Pat, c)]
  deriving (Show)

$(deriveShow1 ''ValueF)

$(deriveShow1 ''CompF)

newtype Value =
  Value (Cofree (ValueF Comp) Meta)
  deriving (Show)

newtype Comp =
  Comp (Cofree (CompF Value) Meta)
  deriving (Show)

data Term
  = TermValue Value
  | TermComp Comp
  deriving (Show)

data WeakTermF a
  = WeakTermVar Identifier
  | WeakTermConst Identifier
  | WeakTermNodeApp Identifier
                    [a]
  | WeakTermThunk a
  | WeakTermLam (Identifier, WeakType)
                a
  | WeakTermApp a
                a
  | WeakTermRet a
  | WeakTermBind (Identifier, WeakType)
                 a
                 a
  | WeakTermUnthunk a
  | WeakTermMu (Identifier, WeakType)
               a
  | WeakTermCase a
                 [(Pat, a)]
  | WeakTermAsc a
                WeakType

$(deriveShow1 ''WeakTermF)

deriving instance Show a => Show (WeakTermF a)

deriving instance Functor WeakTermF

type WeakTerm = Cofree WeakTermF Meta

instance (Show a) => Show (IORef a) where
  show a = show (unsafePerformIO (readIORef a))

data Env = Env
  { count         :: Int -- to generate fresh symbols
  , valueEnv      :: [(Identifier, ValueType)] -- values and its types
  , notationEnv   :: [(Tree, Tree)] -- macro transformers
  , reservedEnv   :: [Identifier] -- list of reserved keywords
  , nameEnv       :: [(Identifier, Identifier)] -- used in alpha conversion
  , weakTypeEnv   :: [(Identifier, WeakType)] -- used in type inference
  , typeEnv       :: [(Identifier, Type)] -- polarized type environment
  , constraintEnv :: [(WeakType, WeakType)] -- used in type inference
  , levelEnv      :: [(WeakLevel, WeakLevel)] -- constraint regarding the level of universes
  , argEnv        :: [(IdentOrHole, IdentOrHole)] -- equivalence of arguments of forall
  , thunkEnv      :: [(Identifier, Identifier)]
  , codeEnv       :: [(Identifier, IORef Code)] -- quoted codes (should be ioref?)
  } deriving (Show)

initialEnv :: Env
initialEnv =
  Env
    { count = 0
    , valueEnv = []
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
    , constraintEnv = []
    , levelEnv = []
    , thunkEnv = []
    , argEnv = []
    , codeEnv = []
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
  return $ "#" ++ show i

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

lookupVEnv :: String -> WithEnv (Maybe ValueType)
lookupVEnv s = gets (lookup s . valueEnv)

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

lookupCodeEnv :: Identifier -> WithEnv (Maybe (IORef Code))
lookupCodeEnv s = gets (lookup s . codeEnv)

insWTEnv :: String -> WeakType -> WithEnv ()
insWTEnv s t = modify (\e -> e {weakTypeEnv = (s, t) : weakTypeEnv e})

insCEnv :: WeakType -> WeakType -> WithEnv ()
insCEnv t1 t2 = modify (\e -> e {constraintEnv = (t1, t2) : constraintEnv e})

insLEnv :: WeakLevel -> WeakLevel -> WithEnv ()
insLEnv l1 l2 = modify (\e -> e {levelEnv = (l1, l2) : levelEnv e})

insAEnv :: IdentOrHole -> IdentOrHole -> WithEnv ()
insAEnv x y = modify (\e -> e {argEnv = (x, y) : argEnv e})

insThunkEnv :: Identifier -> Identifier -> WithEnv ()
insThunkEnv i j = modify (\e -> e {thunkEnv = (i, j) : thunkEnv e})

insCodeEnv :: Identifier -> IORef Code -> WithEnv ()
insCodeEnv i code = modify (\e -> e {codeEnv = (i, code) : codeEnv e})

local :: WithEnv a -> WithEnv a
local p = do
  env <- get
  x <- p
  modify (\e -> env {count = count e})
  return x

data Data
  = DataPointer Identifier -- var is something that points already-allocated data
  | DataCell Identifier -- value of defined data types
             [Data]
  | DataLabel Identifier -- the address of quoted code.
  deriving (Show, Eq)

data Code
  = CodeAllocate Data -- return
  | CodeLet Identifier -- bind (we also use this to represent application)
            Data
            Code
  | CodeJump Identifier -- unthunk
             Identifier -- this second argument is required to lookup the corresponding code
  deriving (Show, Eq)
