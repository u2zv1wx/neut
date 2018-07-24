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
  | Node [MTree]
  deriving (Show, Eq)

car :: Tree -> Maybe MTree
car (Node (t:_)) = Just t
car _            = Nothing

cdr :: Tree -> Maybe [MTree]
cdr (Node (_:ts)) = Just ts
cdr _             = Nothing

ith :: Int -> Tree -> Maybe MTree
-- ith 1 (Atom s) = Just (Atom s)
ith i (Node ts)
  | 0 < i && i <= length ts = Just $ ts !! (i - 1)
ith _ _ = Nothing

treeLength :: Tree -> Int
treeLength (Atom _)  = 1
treeLength (Node ts) = length ts

recurM :: (Monad m) => (MTree -> m MTree) -> MTree -> m MTree
recurM f (Atom s, i) = f (Atom s, i)
recurM f (Node tis, i) = do
  tis' <- mapM (recurM f) tis
  f (Node tis', i)

type MTree = (Tree, Identifier)

data Sym =
  S String
    MType
  deriving (Show, Eq)

data Level
  = Fixed Int
  | LHole String
  deriving (Show, Eq)

type ClosureName = String

type FreeVar = String

type Identifier = String

-- positive term / value
-- v ::= x
--     | {defined constant} <- such as nat, succ, etc.
--     | (v v)
--     | (thunk e)
--     | (ascribe v P)
data V
  = VVar String
  | VConst String
  | VThunk MC
  | VConsApp MV
             MV
  | VAsc MV
         MType
  deriving (Show, Eq)

-- value with metadata
type MV = (V, Identifier)

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
         MC
  | CApp MC
         MV
  | CRet MV
  | CBind Sym
          MC
          MC
  | CUnthunk MV
  | CSend Sym
          MC
  | CRecv Sym
          MC
  | CDispatch MC
              MC
  | CColeft MC
  | CCoright MC
  | CMu Sym
        MC
  | CCase MC
          [(MV, MC)]
  | CAsc MC
         MType
  deriving (Show, Eq)

-- computation with identifier
type MC = (C, Identifier)

data PolTerm
  = Value MV
  | Comp MC
  deriving (Show, Eq)

data Term
  = Var String
  | Const String
  | Thunk MTerm
  | Lam Sym
        MTerm
  | App MTerm
        MTerm
  | ConsApp MTerm
            MTerm
  | Ret MTerm
  | Bind Sym
         MTerm
         MTerm
  | Unthunk MTerm
  | Send Sym
         MTerm
  | Recv Sym
         MTerm
  | Dispatch MTerm
             MTerm
  | Coleft MTerm
  | Coright MTerm
  | Mu Sym
       MTerm
  | Case MTerm
         [(MTerm, MTerm)]
  | Asc MTerm
        MType
  deriving (Show, Eq)

type MTerm = (Term, Identifier)

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
          MType
  | TUp MType
  | TDown MType
  | TUniv Level
  | TForall Sym
            MType
  | TCotensor MType
              MType
  deriving (Show, Eq)

type MType = (Type, Identifier)

data Env = Env
  { count         :: Int
  , valueEnv      :: [(String, MType)]
  , notationEnv   :: [(MTree, MTree)]
  , reservedEnv   :: [String]
  , nameEnv       :: [(String, String)]
  , exprEnv       :: [Term]
  , typeEnv       :: [(String, Type)]
  , constraintEnv :: [(Type, Type)]
  , levelEnv      :: [(Level, Level)]
  , clsEnv        :: [(ClosureName, [FreeVar], Term)]
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

lookupVEnv :: String -> WithEnv (Maybe MType)
lookupVEnv s = gets (lookup s . valueEnv)

insTEnv :: String -> Type -> WithEnv ()
insTEnv s t = modify (\e -> e {typeEnv = (s, t) : typeEnv e})

insCEnv :: Type -> Type -> WithEnv ()
insCEnv t1 t2 = modify (\e -> e {constraintEnv = (t1, t2) : constraintEnv e})

insLEnv :: Level -> Level -> WithEnv ()
insLEnv l1 l2 = modify (\e -> e {levelEnv = (l1, l2) : levelEnv e})

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
  | LoadConst MemAddr -- the address of constants (such as `nat`, `succ`, etc.)
  | ConstCell Cell -- create a new cons cell and return the newly allocated memory address
  | Alloc Operation -- thunk code <list of free var>
          [RegName]
  deriving (Show, Eq)

data Operation
  = Ans Operand -- return
  | Let RegName -- bind (we also use this to represent abstraction/application)
        Operand
        Operation
  | Jump RegName -- unthunk (jump to the address in the register)
  deriving (Show, Eq)
