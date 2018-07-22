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
    Type
  deriving (Show, Eq)

data Level
  = Fixed Int
  | LHole String
  deriving (Show, Eq)

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
--     | (coleft e)
--     | (coright e)
--     | (mu (x P) e)
--     | (case e (v1 e1) ... (vn en))
--     | (ascribe e N)
data Expr
  = Var String
  | Const Sym
  | Thunk Expr
  | Lam Sym
        Expr
  | App Expr
        Expr
  | Ret Expr
  | Bind Sym
         Expr
         Expr
  | Unthunk Expr
  | Send Sym
         Expr
  | Recv Sym
         Expr
  | Dispatch Expr
             Expr
  | Coleft Expr
  | Coright Expr
  | Mu Sym
       Expr
  | Case Expr
         [(Expr, Expr)]
  | Asc Expr
        Type
  deriving (Show, Eq)

-- positive type
-- P ::= p
--     | (down N)
--     | {defined constant type}
--     | (constructor (x P) P)
--     | (universe i)
-- negative type
-- N ::= (forall (x P) N)
--     | (cotensor N1 ... Nn)
--     | (up P)
data Type
  = TVar String
  | THole String
  | TConst Sym
  | TImp Sym
         Type
  | TUp Type
  | TDown Type
  | TUniv Level
  | TForall Sym
            Type
  | TCotensor Type
              Type
  deriving (Show, Eq)

-- value definition
-- V ::= (value x P)
-- newtype VDef = VDef
--   { consName :: Sym
--   } deriving (Show, Eq)
-- data Term =
--   Expr E
--   -- | ValueDefinition VDef
--   deriving (Show, Eq)
-- type Program = [Term]
data Env = Env
  { count         :: Int
  , valueEnv      :: [Sym]
  , notationEnv   :: [(Tree, Tree)]
  , reservedEnv   :: [String]
  , nameEnv       :: [(String, String)]
  , exprEnv       :: [Expr]
  , typeEnv       :: [(String, Type)]
  , constraintEnv :: [(Type, Type)]
  , levelEnv      :: [(Level, Level)]
  , posEnv        :: [Type]
  , negEnv        :: [Type]
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
    , exprEnv = []
    , typeEnv = []
    , constraintEnv = []
    , levelEnv = []
    , posEnv = []
    , negEnv = []
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
  s' <- newName
  return $ s ++ s'

lookupTEnv :: String -> WithEnv (Maybe Type)
lookupTEnv s = gets (lookup s . typeEnv)

insTEnv :: String -> Type -> WithEnv ()
insTEnv s t = modify (\e -> e {typeEnv = (s, t) : typeEnv e})

insCEnv :: Type -> Type -> WithEnv ()
insCEnv t1 t2 = modify (\e -> e {constraintEnv = (t1, t2) : constraintEnv e})

insPosEnv :: Type -> WithEnv ()
insPosEnv t = modify (\e -> e {posEnv = t : posEnv e})

insNegEnv :: Type -> WithEnv ()
insNegEnv t = modify (\e -> e {negEnv = t : negEnv e})

insLEnv :: Level -> Level -> WithEnv ()
insLEnv l1 l2 = modify (\e -> e {levelEnv = (l1, l2) : levelEnv e})
