module Data where

import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Data.Maybe                 (fromMaybe)

import qualified Text.Show.Pretty           as Pr

type Sym = String

data Tree
  = Atom Sym
  | Node [Tree]
  deriving (Show, Eq)

car :: Tree -> Maybe Tree
car (Node (t:_)) = Just t
car _            = Nothing

cdr :: Tree -> Maybe [Tree]
cdr (Node (_:ts)) = Just ts
cdr _             = Nothing

ith :: Int -> Tree -> Maybe Tree
ith 1 (Atom s) = Just (Atom s)
ith i (Node ts)
  | 0 < i && i <= length ts = Just $ ts !! (i - 1)
ith _ _ = Nothing

treeLength :: Tree -> Int
treeLength (Atom _)  = 1
treeLength (Node ts) = length ts

recurM :: (Monad m) => (Tree -> m Tree) -> Tree -> m Tree
recurM f (Atom s) = f (Atom s)
recurM f (Node ts) = do
  ts' <- mapM (recurM f) ts
  f (Node ts')

type Level = Int

-- positive term
-- v ::= x
--     | (quote e)
--     | {defined constant} <- such as nat, succ, etc.
--     | (v v)
--     | (ascribe v P)
data V
  = Var Sym
  | Quote E
  | VAtom ValueDef
  | VApp V
         V
  | VAsc V
         P
  deriving (Show, Eq)

-- negative term
-- e ::= (lambda x e)
--     | (e v)
--     | (return v)
--     | (bind x e1 e2)
--     | (unquote v)
--     | (send x e)
--     | (receive x e)
--     | (dispatch e1 ... en)
--     | (select i e)
--     | (mu x e)
--     | (case e (v1 e1) ... (vn en))
--     | (ascribe e N)
data E
  = Lam Sym
        E
  | App E
        V
  | Ret V
  | Bind Sym
         E
         E
  | Unquote V
  | Send Sym
         E
  | Receive Sym
            E
  | Dispatch [E]
  | Select Int
           E
  | Mu Sym
       E
  | Case E
         [(V, E)]
  | NAsc E
         N
  deriving (Show, Eq)

-- positive type
-- P ::= p
--     | (down N)
--     | {defined constant type}
--     | (constructor (x P) P)
--     | (universe i)
data P
  = PVar Sym
  | Down N
  | PAtom ValueDef
  | PImp Sym
         P
         P
  | Universe Level
  deriving (Show, Eq)

-- negative type
-- N ::= n
--     | (forall (x P) N)
--     | (par N1 ... Nn)
--     | (up P)
data N
  = NVar Sym
  | Up P
  | Forall Sym
           P
           N
  | Par [N]
  deriving (Show, Eq)

-- value definition
-- V ::= (value x P)
data ValueDef = ValueDef
  { consName :: Sym
  , consType :: P
  } deriving (Show, Eq)

data Env = Env
  { i           :: Int
  , valueEnv    :: [ValueDef]
  , notationEnv :: [(Tree, Tree)]
  , reservedEnv :: [Sym]
  , compEnv     :: [E]
  } deriving (Show)

initialEnv :: Env
initialEnv =
  Env
    { i = 0
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
    , compEnv = []
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
