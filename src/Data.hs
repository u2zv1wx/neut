{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveFoldable       #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Data where

import           Control.Comonad
import           Control.Comonad.Cofree
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.Functor.Classes
import           Text.Show.Deriving

import           Data.Maybe                 (fromMaybe)

import qualified Text.Show.Pretty           as Pr

-- S-expression
data Tree a
  = Atom String
  | Node [a]
  deriving (Foldable)

deriving instance Show a => Show (Tree a)

newtype Meta = Meta
  { ident :: String
  } deriving (Show, Eq)

$(deriveShow1 ''Tree)

type MTree = Cofree Tree Meta

recurM :: (Monad m) => (MTree -> m MTree) -> MTree -> m MTree
recurM f (meta :< Atom s) = f (meta :< Atom s)
recurM f (meta :< Node tis) = do
  tis' <- mapM (recurM f) tis
  f (meta :< Node tis')

-- positive type
-- P ::= p
--     | (down N)
--     | {defined constant type}
--     | (node (x P) P)
--     | (universe i)
-- negative type
-- N ::= (forall (x P) N)
--     | (cotensor N1 ... Nn)
--     | (up P)
data Type
  = TVar String
  | THole String
  | TConst String
  | TUp Type
  | TDown Type
  | TUniv Level
  | TForall Sym
            Type
  deriving (Show, Eq)

type Sym = (String, Type)

data Level
  = Fixed Int
  | LHole String
  deriving (Show, Eq)

type Identifier = String

-- positive term / value
-- v ::= x
--     | {defined constant} <- such as nat, succ, etc.
--     | (v v)
--     | (thunk e)
--     | (ascribe v P)
data V c v
  = VVar String
  | VConst String
  | VThunk c
  | VAsc v
         Type
  deriving (Eq)

-- negative term / computation
-- e ::= (lambda (x P) e)
--     | (e v)
--     | (return v)
--     | (bind (x P) e1 e2)
--     | (unthunk v)
--     | (send (x P) e)
--     | (receive (x P) e)
--     | (dispatch e1 ... en)
--     | (coleft e)
--     | (coright e)
--     | (mu (x P) e)
--     | (case e (v1 e1) ... (vn en))
--     | (ascribe e N)
data C v c
  = CLam Sym
         c
  | CApp c
         v
  | CRet v
  | CBind Sym
          c
          c
  | CUnthunk v
  | CMu Sym
        c
  | CCase v
          [(v, c)]
  | CAsc c
         Type
  deriving (Eq)

$(deriveShow1 ''V)

$(deriveShow1 ''C)

newtype MV =
  MV (Cofree (V MC) Meta)
  deriving (Show)

newtype MC =
  MC (Cofree (C MV) Meta)
  deriving (Show)

-- computation with identifier
-- type MC = (C, Meta)
data PolTerm
  = Value MV
  | Comp MC
  deriving (Show)

data PatF a
  = PatVar String
  | PatConst String
  | PatApp a
           a
  deriving (Show, Eq)

$(deriveShow1 ''PatF)

type Pat = Cofree PatF Meta

data Term a
  = Var String
  | Const String
  | Thunk a
  | Lam Sym
        a
  | App a
        a
  | Ret a
  | Bind Sym
         a
         a
  | Unthunk a
  | Mu Sym
       a
  | Case a
         [(Pat, a)]
  | Asc a
        Type

$(deriveShow1 ''Term)

deriving instance Show a => Show (Term a)

type MTerm = Cofree Term Meta

data Env = Env
  { count             :: Int
  , valueEnv          :: [(String, Type)]
  , notationEnv       :: [(MTree, MTree)]
  , reservedEnv       :: [String]
  , nameEnv           :: [(String, String)]
  , typeEnv           :: [(String, Type)]
  , constraintEnv     :: [(Type, Type)]
  , nameConstraintEnv :: [(Sym, Sym)]
  , levelEnv          :: [(Level, Level)]
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
    , nameConstraintEnv = []
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

newName :: WithEnv String
newName = do
  env <- get
  let i = count env
  modify (\e -> e {count = i + 1})
  return $ "#" ++ show i

newNameWith :: String -> WithEnv String
newNameWith s = do
  i <- newName
  let s' = s ++ i
  modify (\e -> e {nameEnv = (s, s') : nameEnv e})
  return s'

lookupTEnv :: String -> WithEnv (Maybe Type)
lookupTEnv s = gets (lookup s . typeEnv)

lookupVEnv :: String -> WithEnv (Maybe Type)
lookupVEnv s = gets (lookup s . valueEnv)

insTEnv :: String -> Type -> WithEnv ()
insTEnv s t = modify (\e -> e {typeEnv = (s, t) : typeEnv e})

insCEnv :: Type -> Type -> WithEnv ()
insCEnv t1 t2 = modify (\e -> e {constraintEnv = (t1, t2) : constraintEnv e})

insNCEnv :: Sym -> Sym -> WithEnv ()
insNCEnv s1 s2 =
  modify (\e -> e {nameConstraintEnv = (s1, s2) : nameConstraintEnv e})

insLEnv :: Level -> Level -> WithEnv ()
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
