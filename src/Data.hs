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

import qualified Text.Show.Pretty           as Pr

type Identifier = String

newtype Meta = Meta
  { ident :: Identifier
  } deriving (Show, Eq)

-- level of universe
data WeakLevel
  = Fixed Int
  | LHole Identifier
  deriving (Show, Eq)

type Level = Int

-- S-expression
data SExpF a
  = SAtom Identifier
  | SNode [a]

deriving instance Show a => Show (SExpF a)

$(deriveShow1 ''SExpF)

type Tree = Cofree SExpF Meta

recurM :: (Monad m) => (Tree -> m Tree) -> Tree -> m Tree
recurM f (meta :< SAtom s) = f (meta :< SAtom s)
recurM f (meta :< SNode tis) = do
  tis' <- mapM (recurM f) tis
  f (meta :< SNode tis')

-- weaktype
-- WT ::= P | N
data WeakType
  = WTVar Identifier
  | WTHole Identifier
  | WTConst Identifier
  | WTUp WeakType
  | WTDown WeakType
  | WTUniv WeakLevel
  | WTForall (Identifier, WeakType)
             WeakType
  deriving (Show, Eq)

-- value type
-- P ::= p
--     | (down N)
--     | {defined constant type}
--     | (node (x P) P)
--     | (universe i)
data ValueType
  = VTVar Identifier
  | VTConst Identifier
  | VTDown CompType
  | VTUniv Level
  deriving (Show, Eq)

-- computation type
-- N ::= (forall (x P) N)
--     | (cotensor N1 ... Nn)
--     | (up P)
data CompType
  = CTForall (Identifier, ValueType)
             CompType
  | CTUp CompType
  deriving (Show, Eq)

-- value / positive term
-- v ::= x
--     | {defined constant} <- such as nat, succ, etc.
--     | (v v)
--     | (thunk e)
--     | (ascribe v P)
data ValueF c v
  = VVar Identifier
  | VConst Identifier
  | VThunk c
  | VAsc v
         ValueType
  deriving (Eq)

-- computation / negative term
-- e ::= (lambda (x P) e)
--     | (e v)
--     | (return v)
--     | (bind (x P) e1 e2)
--     | (unthunk v)
--     | (mu (x P) e)
--     | (case e (v1 e1) ... (vn en))
--     | (ascribe e N)
data CompF v c
  = CLam (Identifier, ValueType)
         c
  | CApp c
         v
  | CRet v
  | CBind (Identifier, ValueType)
          c
          c
  | CUnthunk v
  | CMu (Identifier, ValueType)
        c
  | CCase v
          [(v, c)]
  | CAsc c
         CompType
  deriving (Eq)

$(deriveShow1 ''ValueF)

$(deriveShow1 ''CompF)

newtype Value =
  Value (Cofree (ValueF Comp) Meta)
  deriving (Show)

newtype Comp =
  Comp (Cofree (CompF Value) Meta)
  deriving (Show)

data Term
  = TValue Value
  | TComp Comp
  deriving (Show)

data PatF a
  = PVar Identifier
  | PConst Identifier
  | PApp a
         a
  deriving (Show, Eq)

$(deriveShow1 ''PatF)

type Pat = Cofree PatF Meta

data WeakTermF a
  = Var Identifier
  | Const Identifier
  | Thunk a
  | Lam (Identifier, WeakType)
        a
  | App a
        a
  | Ret a
  | Bind (Identifier, WeakType)
         a
         a
  | Unthunk a
  | Mu (Identifier, WeakType)
       a
  | Case a
         [(Pat, a)]
  | Asc a
        WeakType

$(deriveShow1 ''WeakTermF)

deriving instance Show a => Show (WeakTermF a)

type WeakTerm = Cofree WeakTermF Meta

data Env = Env
  { count         :: Int -- to generate fresh symbols
  , valueEnv      :: [(Identifier, ValueType)] -- values and its types
  , notationEnv   :: [(Tree, Tree)] -- macro transformers
  , reservedEnv   :: [Identifier] -- list of reserved keywords
  , nameEnv       :: [(Identifier, Identifier)] -- used in alpha conversion
  , typeEnv       :: [(Identifier, WeakType)] -- used in type inference
  , constraintEnv :: [(WeakType, WeakType)] -- used in type inference
  , levelEnv      :: [(WeakLevel, WeakLevel)] -- constraint regarding the level of universes
  } deriving (Show)

initialEnv :: Env
initialEnv =
  Env
    { count = 0
    , valueEnv = []
    , notationEnv = []
    , reservedEnv =
        [ "quote"
        , "lambda"
        , "return"
        , "bind"
        , "unquote"
        , "send"
        , "receive"
        , "dispatch"
        , "select"
        , "mu"
        , "case"
        , "ascribe"
        , "down"
        , "universe"
        , "forall"
        , "par"
        , "up"
        ]
    , nameEnv = []
    , typeEnv = []
    , constraintEnv = []
    , levelEnv = []
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

lookupTEnv :: String -> WithEnv (Maybe WeakType)
lookupTEnv s = gets (lookup s . typeEnv)

lookupVEnv :: String -> WithEnv (Maybe ValueType)
lookupVEnv s = gets (lookup s . valueEnv)

insTEnv :: String -> WeakType -> WithEnv ()
insTEnv s t = modify (\e -> e {typeEnv = (s, t) : typeEnv e})

insCEnv :: WeakType -> WeakType -> WithEnv ()
insCEnv t1 t2 = modify (\e -> e {constraintEnv = (t1, t2) : constraintEnv e})

insLEnv :: WeakLevel -> WeakLevel -> WithEnv ()
insLEnv l1 l2 = modify (\e -> e {levelEnv = (l1, l2) : levelEnv e})

local :: WithEnv a -> WithEnv a
local p = do
  env <- get
  x <- p
  modify (\e -> env {count = count e})
  return x

type Addr = String

type RegName = String

type MemAddr = String

data Cell
  = CellAtom String
  | CellReg RegName
  | CellCons Cell
             Cell
  deriving (Show, Eq)

data Operand
  = Register RegName -- var
  | ConstCell Cell -- create a new cons cell and return the newly allocated memory address
  | Alloc Operation -- thunk code <list of free var>
          [RegName]
  deriving (Show, Eq)

data Operation
  = Ans Operand -- return
  | Let RegName -- bind (we also use this to represent abstraction/application)
        Operand
        Operation
  | LetCall RegName -- binding the result of unthunk
            MemAddr
            Operation
  | Jump RegName -- unthunk
  deriving (Show, Eq)
