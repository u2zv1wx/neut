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
import           Data.List

import           Data.Functor.Foldable

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

-- data Case a
--   = CaseSwitch Identifier
--                a -- the name of constructor
--   | CaseDefault [Identifier]
--                 a -- arguments
--   deriving (Show)
-- deriving instance Functor Case
-- $(deriveShow1 ''Case)
data Decision a
  = DecisionLeaf [(Occurrence, (Identifier, ValueType))]
                 a
  | DecisionSwitch Occurrence
                   [(Identifier, Decision a)]
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
  = LowTypeConst
  | LowTypeNull
  | LowTypeVec Identifier -- the type of cons cell
               [LowType]
  | LowTypeSwitch [LowType]
  deriving (Show)

data DataF a
  = DataPointer Identifier -- var is something that points already-allocated data
  | DataCell Identifier -- value of defined data types
             [a]
  | DataLabel Identifier -- the address of quoted code
  | DataElemAtIndex a -- subvalue of an inductive value
                    Index
  -- deriving (Show, Eq)

deriving instance Show a => Show (DataF a)

deriving instance Functor DataF

$(deriveShow1 ''DataF)

type Data = Cofree DataF LowType

type UData = Fix DataF

-- newtype Fix f =
--   In (f (Fix f))
-- $(deriveShow1 ''Fix)
type Branch = (Identifier, Identifier)

type DefaultBranch = Identifier

data CodeF d a
  = CodeReturn d -- return
  | CodeLet Identifier -- bind (we also use this to represent application)
            d
            a
  | CodeSwitch d -- branching in pattern-matching (elimination of inductive type)
               DefaultBranch
               [Branch]
  | CodeCall Identifier -- the result of call
             Identifier -- the label of the funtion
             [Identifier] -- arguments
             a -- continuation
  | CodeJump Identifier -- unthunk
             Identifier -- this second argument is required to lookup the corresponding code
             [Identifier] -- list of arguments

deriving instance Show a => Show (CodeF UData a)

deriving instance Show a => Show (CodeF Data a)

deriving instance Functor (CodeF UData)

deriving instance Functor (CodeF Data)

$(deriveShow1 ''CodeF)

type Code = Cofree (CodeF Data) LowType

type UCode = Fix (CodeF UData)

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
  , compTypeEnv    :: [(Identifier, CompType)]
  , constraintEnv  :: [(WeakType, WeakType)] -- used in type inference
  , levelEnv       :: [(WeakLevel, WeakLevel)] -- constraint regarding the level of universes
  , argEnv         :: [(IdentOrHole, IdentOrHole)] -- equivalence of arguments of forall
  , thunkEnv       :: [(Identifier, Identifier)]
  , funEnv         :: [(Identifier, IORef [(Identifier, IORef UCode)])]
  , lowTypeEnv     :: [(Identifier, LowType)]
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
    , compTypeEnv = []
    , constraintEnv = []
    , levelEnv = []
    , thunkEnv = []
    , argEnv = []
    , funEnv = []
    , lowTypeEnv = []
    , scope = "main"
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

lookupFunEnv :: Identifier -> WithEnv (IORef [(Identifier, IORef UCode)])
lookupFunEnv s = do
  m <- gets (lookup s . funEnv)
  case m of
    Nothing -> lift $ throwE $ "no such function: " ++ show s
    Just k  -> return k

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

lookupCodeEnv :: Identifier -> WithEnv (Maybe (IORef UCode))
lookupCodeEnv s = do
  current <- getFunName
  codeEnvRef <- lookupFunEnv current
  codeEnv <- liftIO $ readIORef codeEnvRef
  return $ lookup s codeEnv

lookupConstructorEnv :: Identifier -> WithEnv [Identifier]
lookupConstructorEnv cons = do
  env <- get
  case lookup cons (constructorEnv env) of
    Nothing -> lift $ throwE $ "no such constructor defined: " ++ show cons
    Just cenvRef -> liftIO $ readIORef cenvRef

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
  mt <- lookupLowTypeEnv s
  case mt of
    Just t -> return t
    Nothing -> do
      lift $ throwE $ "the type of " ++ show s ++ " is not defined "

lookupValueTypeEnv :: String -> WithEnv (Maybe ValueType)
lookupValueTypeEnv s = gets (lookup s . valueTypeEnv)

lookupValueTypeEnv' :: String -> WithEnv ValueType
lookupValueTypeEnv' s = do
  mt <- lookupValueTypeEnv s
  case mt of
    Just t -> return t
    Nothing -> do
      lift $ throwE $ "the type of " ++ show s ++ " is not defined "

insCTEnv :: String -> CompType -> WithEnv ()
insCTEnv s t = modify (\e -> e {compTypeEnv = (s, t) : compTypeEnv e})

lookupCompTypeEnv :: String -> WithEnv (Maybe CompType)
lookupCompTypeEnv s = gets (lookup s . compTypeEnv)

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

insCodeEnv :: Identifier -> IORef UCode -> WithEnv ()
insCodeEnv i code = do
  current <- getFunName
  codeEnvRef <- lookupFunEnv current
  codeEnv <- liftIO $ readIORef codeEnvRef
  liftIO $ writeIORef codeEnvRef $ (i, code) : codeEnv

insEmptyFunEnv :: Identifier -> WithEnv ()
insEmptyFunEnv i = do
  x <- liftIO $ newIORef []
  modify (\e -> e {funEnv = (i, x) : funEnv e})

setFunName :: Identifier -> WithEnv ()
setFunName i = do
  modify (\e -> e {scope = i})

getFunName :: WithEnv Identifier
getFunName = do
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
