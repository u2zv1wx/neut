module Data where

import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Data.Maybe                 (fromMaybe)

import qualified Text.Show.Pretty           as Pr

type Sym = String

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

-- constructor definition
-- C ::= (value x P)
data ValueDef = ValueDef
  { consName :: Sym
  , consType :: P
  } deriving (Show, Eq)

-- data WeakForm
--   = WeakFormHole
--   | WeakFormSym String
--   | WeakFormApp WeakForm
--                 [WeakForm]
--   deriving (Show)
-- -- form ::= strong-form | (strong-form weak-form1 ... weak-formn)
-- data Form
--   = Form String
--          [WeakForm]
--   | FormWithRest String
--                  [WeakForm]
--   deriving (Show)
-- unifyFormV :: Form -> V -> Either String ([(String, Term)], Maybe [Term])
-- unifyFormV (Form s ws) (APP (VPosSym (PosSym (S s'))) xs)
--   | s /= s' = Left $ "Cannot match " ++ show s ++ " with " ++ show s'
--   | length ws /= length xs =
--     Left $ "Cannot match " ++ show ws ++ " with " ++ show xs
--   | otherwise = do
--     ys <- zipWithM unifyEWeakForm ws xs
--     return (concat ys, Nothing)
-- unifyFormV (FormWithRest s ws) (APP (VPosSym (PosSym (S s'))) xs)
--   | s /= s' = Left $ "Cannot match " ++ show s ++ " with " ++ show s'
--   | length ws > length xs =
--     Left $ "Cannot match " ++ show ws ++ " with " ++ show xs
--   | otherwise = do
--     ys <- zipWithM unifyEWeakForm ws xs
--     let rest = drop (length ws) xs
--     return (concat ys, Just (map NegTerm rest))
-- unifyFormV f v = Left $ "Cannot match " ++ show f ++ " with " ++ show v
-- unifyFormE :: Form -> E -> Either String ([(String, Term)], Maybe [Term])
-- unifyFormE (Form s ws) (App (ENegSym (NegSym (S s'))) xs)
--   | s /= s' = Left $ "Cannot match " ++ show s ++ " with " ++ show s'
--   | length ws /= length xs =
--     Left $ "Cannot match " ++ show ws ++ " with " ++ show xs
--   | otherwise = do
--     ys <- zipWithM unifyVWeakForm ws xs
--     return (concat ys, Nothing)
-- unifyFormE (FormWithRest s ws) (App (ENegSym (NegSym (S s'))) xs)
--   | s /= s' = Left $ "Cannot match " ++ show s ++ " with " ++ show s'
--   | length ws > length xs =
--     Left $ "Cannot match " ++ show ws ++ " with " ++ show xs
--   | otherwise = do
--     ys <- zipWithM unifyVWeakForm ws xs
--     let rest = drop (length ws) xs
--     return (concat ys, Just (map PosTerm rest))
-- unifyFormE f v = Left $ "Cannot match " ++ show f ++ " with " ++ show v
-- unifyVWeakForm :: WeakForm -> V -> Either String [(String, Term)]
-- unifyVWeakForm WeakFormHole _ = return []
-- unifyVWeakForm (WeakFormSym s) v = return [(s, PosTerm v)]
-- unifyVWeakForm (WeakFormApp s args) (APP v es) = do
--   subst1 <- unifyVWeakForm s v
--   subst2 <- zipWithM unifyEWeakForm args es
--   return $ subst1 ++ concat subst2
-- unifyVWeakForm f v = Left $ "Cannot match " ++ show f ++ " against " ++ show v
-- unifyEWeakForm :: WeakForm -> E -> Either String [(String, Term)]
-- unifyEWeakForm WeakFormHole _ = return []
-- unifyEWeakForm (WeakFormSym s) e = return [(s, NegTerm e)]
-- unifyEWeakForm (WeakFormApp s args) (App e vs) = do
--   subst1 <- unifyEWeakForm s e
--   subst2 <- zipWithM unifyVWeakForm args vs
--   return $ subst1 ++ concat subst2
-- unifyEWeakForm f v = Left $ "Cannot match " ++ show f ++ " against " ++ show v
data Env = Env
  { i           :: Int
  , valueEnv    :: [ValueDef]
  -- , vNotationEnv :: [(String, Form, V)]
  -- , eNotationEnv :: [(String, Form, E)]
  , reservedEnv :: [String]
  , compEnv     :: [E]
  } deriving (Show)

initialEnv :: Env
initialEnv =
  Env
    { i = 0
    , valueEnv = []
    -- , vNotationEnv = []
    -- , eNotationEnv = []
    , reservedEnv = []
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
