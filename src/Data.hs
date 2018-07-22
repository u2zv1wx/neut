module Data where

import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Data.Maybe                 (fromMaybe)

import qualified Text.Show.Pretty           as Pr

-- S-expression
data Tree
  = Atom String
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

data Sym =
  S String
    T
  deriving (Show, Eq)

type Level = Int

-- positive term
-- v ::= x
--     | {defined constant} <- such as nat, succ, etc.
--     | (v v)
--     | (thunk e)
--     | (ascribe v P)
-- negative term
-- e ::= (lambda (x P) e)
--     | (e v)
--     | (return v)
--     | (bind (x P) e1 e2)
--     | (unthunk v)
--     | (send (x P) e)
--     | (receive (x P) e)
--     | (dispatch e1 ... en)
--     | (select i e)
--     | (mu (x P) e)
--     | (case e (v1 e1) ... (vn en))
--     | (ascribe e N)
data E
  = Var String
  | VAtom VDef
  | Thunk E
  | Lam Sym
        E
  | App E
        E
  | Ret E
  | Bind Sym
         E
         E
  | Unthunk E
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
         [(E, E)]
  | Asc E
        T
  deriving (Show, Eq)

-- positive type
-- P ::= p
--     | (down N)
--     | {defined constant type}
--     | (constructor (x P) P)
--     | (universe i)
-- negative type
-- N ::= (forall (x P) N)
--     | (par N1 ... Nn)
--     | (up P)
data T
  = PVar String
  | THole String
  | PAtom VDef
  | PImp Sym
         T
  | Down T
  | Universe Level
  | Forall Sym
           T
  | Up T
  | Par [T]
  deriving (Show, Eq)

-- value definition
-- V ::= (value x P)
newtype VDef = VDef
  { consName :: Sym
  } deriving (Show, Eq)

data Term
  = Expr E
  | ValueDefinition VDef
  deriving (Show, Eq)

type Program = [Term]

data Env = Env
  { count       :: Int
  , valueEnv    :: [VDef]
  , notationEnv :: [(Tree, Tree)]
  , reservedEnv :: [String]
  , compEnv     :: [E]
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

newName :: WithEnv String
newName = do
  env <- get
  let i = count env
  modify (\e -> e {count = i + 1})
  return $ "#" ++ show i

tryOptions' :: [a -> WithEnv b] -> a -> String -> WithEnv b
tryOptions' [] t err = lift $ throwE err
tryOptions' (k:ks) t err = do
  env <- get
  t' <- liftIO $ runWithEnv (k t) env
  case t' of
    Right (result, env') -> do
      put env'
      return result
    Left err' -> tryOptions' ks t err'

tryOptions :: [a -> WithEnv b] -> a -> WithEnv b
tryOptions k t = tryOptions' k t "There's nothing to try"
