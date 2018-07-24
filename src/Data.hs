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

type ClosureName = String

type FreeVar = String

-- positive term / value
-- v ::= x
--     | {defined constant} <- such as nat, succ, etc.
--     | (v v)
--     | (thunk e)
--     | (ascribe v P)
data V
  = VVar String
  | VConst String
  | VThunk C
  | VConsApp V
             V
  | VAsc V
         Type
  deriving (Show, Eq)

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
data C
  = CLam Sym
         C
  | CApp C
         V
  | CRet V
  | CBind Sym
          C
          C
  | CUnthunk V
  | CSend Sym
          C
  | CRecv Sym
          C
  | CDispatch C
              C
  | CColeft C
  | CCoright C
  | CMu Sym
        C
  | CCase C
          [(V, C)]
  | CAsc C
         Type
  deriving (Show, Eq)

data PolTerm
  = Value V
  | Comp C
  deriving (Show, Eq)

data Term
  = Var String
  | Const String
  | Thunk Term
  | Lam Sym
        Term
  | App Term
        Term
  | ConsApp Term
            Term
  | Ret Term
  | Bind Sym
         Term
         Term
  | Unthunk Term
  | Send Sym
         Term
  | Recv Sym
         Term
  | Dispatch Term
             Term
  | Coleft Term
  | Coright Term
  | Mu Sym
       Term
  | Case Term
         [(Term, Term)]
  | Asc Term
        Type
  deriving (Show, Eq)

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
  | TNode Sym
          Type
  | TUp Type
  | TDown Type
  | TUniv Level
  | TForall Sym
            Type
  | TCotensor Type
              Type
  deriving (Show, Eq)

data Env = Env
  { count         :: Int
  , valueEnv      :: [(String, Type)]
  , notationEnv   :: [(Tree, Tree)]
  , reservedEnv   :: [String]
  , nameEnv       :: [(String, String)]
  , exprEnv       :: [Term]
  , typeEnv       :: [(String, Type)]
  , constraintEnv :: [(Type, Type)]
  , levelEnv      :: [(Level, Level)]
  , clsEnv        :: [(ClosureName, [FreeVar], Term)]
  , defEnv        :: [(String, [Asm])]
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
    , clsEnv = []
    , defEnv = []
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

insLEnv :: Level -> Level -> WithEnv ()
insLEnv l1 l2 = modify (\e -> e {levelEnv = (l1, l2) : levelEnv e})

insDEnv :: String -> [Asm] -> WithEnv ()
insDEnv s d = modify (\e -> e {defEnv = (s, d) : defEnv e})

type Addr = String

data Asm
  = ALoad Addr
  | AJump Addr
  | ACons Addr
          Addr
  | ASetArgs [Addr]
  | AStore Addr
           Addr
  | ARet Addr
  | AAlloc Addr
           [Asm]
           [String]
  | ADeref Addr
  deriving (Show, Eq)

data Operand
  = Register String -- var
  | Alloc Operation -- thunk code <list of free var>
          [Addr]
  deriving (Show, Eq)

data Operation
  = Ans Operand -- return
  | Let String -- bind (we also use this to represent abstraction/application)
        Operand
        Operation
  | Jump Addr -- unthunk
  deriving (Show, Eq)
