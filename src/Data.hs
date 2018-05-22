module Data where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans.Except

import Data.Maybe (fromMaybe)

import qualified Text.Show.Pretty as Pr

data Symbol
  = S String
  | Hole
  | Dots
  deriving (Show, Eq)

-- positive symbol
-- x+ ::= symbol+
--      | (ascribe x+ P)
data PosSym
  = PosSym Symbol
  | PosSymAsc PosSym
              PosType
  deriving (Show)

-- negative symbol
-- x- ::= symbol-
--      | (ascribe x- N)
data NegSym
  = NegSym Symbol
  | NegSymAsc NegSym
              NegType
  deriving (Show)

-- type
-- T ::= P
--     | N
data Type
  = PosType PosType
  | NegType NegType
  deriving (Show)

-- positive type
-- P ::= p
--     | {defined value}
--     | {inverted form of defined computation}
--     | (FORALL ((x1- N1) ... (xn- Nn)) P)
--     | (SWITCH x- N (r1 P1) ... (rn Pn))
--     | (closure N)
--     | positive
data PosType
  = PosTypeSym PosSym
  | ValueApp ValueDef
             [Type]
  | CoCompApp CompDef
              [Type]
  | FORALL [(NegSym, NegType)]
           PosType
  | SWITCH NegSym
           NegType
           [(Refutation, PosType)]
  | Closure NegType
  | PosUniv
  deriving (Show)

-- negative type
-- N ::= n
--     | {defined computation type}
--     | {inverted form of defined value}
--     | (forall ((x1+ P1) ... (xn+ Pn)) N)
--     | (switch x+ P (a1 N1) ... (an Nn))
--     | (CLOSURE P)
--     | negative
data NegType
  = NegTypeSym NegSym
  | CompApp CompDef
            [Type]
  | CoValueApp ValueDef
               [Type]
  | ForAll [(PosSym, PosType)]
           NegType
  | Switch PosSym
           PosType
           [(Assertion, NegType)]
  | CLOSURE PosType
  | NegUniv
  deriving (Show)

-- program
-- z ::= (thread t1) ... (thread tn)
newtype Program =
  Thread [Term]
  deriving (Show)

-- term
-- t ::= v | e
data Term
  = PosTerm V
  | NegTerm E
  deriving (Show)

-- positive term
-- v ::= x
--     | {pattern}
--     | {pattern application}
--     | (LAMBDA (x1 ... xn) v)
--     | (v e1 ... en)
--     | (ZETA x (r1 v1) ... (rn vn))
--     | (ELIM e v)
--     | (thunk e)
--     | (FORCE e)
--     | (quote e)
--     | (ascribe v P)
data V
  = VPosSym PosSym
  | VConsApp ConsDef
             [Term]
  | LAM [NegSym]
        V
  | APP V
        [E]
  | ZETA NegSym
         [(Refutation, V)]
  | APPZETA E
            V
  | Thunk E
  | FORCE E
  | VAsc V
         PosType
  deriving (Show)

-- negative term
-- e ::= x
--     | {pattern}
--     | (lambda (x1 ... xn) e)
--     | (e v1 ... vn)
--     | (zeta x (a1 e1) ... (an en))
--     | (elim v e)
--     | (THUNK v)
--     | (force v)
--     | (unquote v)
--     | (ascribe e N)
data E
  = ENegSym NegSym
  | EConsApp ConsDef
             [Term]
  | Lam [PosSym]
        E
  | App E
        [V]
  | Zeta PosSym
         [(Assertion, E)]
  | AppZeta V
            E
  | THUNK V
  | Force V
  | EAsc E
         NegType
  deriving (Show)

-- pattern ::= a | r
data Pat
  = PosPat Assertion
  | NegPat Refutation
  deriving (Show)

-- assertion pattern
-- a ::= x
--     | [return r]
--     | {etc.}
data Assertion
  = PosAtom PosSym
  | PosConsApp ConsDef
               [Pat]
  deriving (Show)

-- refutation pattern
-- r ::= x
--     | (return a)
--     | {etc.}
data Refutation
  = NegAtom NegSym
  | NegConsApp ConsDef
               [Pat]
  deriving (Show)

inclusionA :: Assertion -> V
inclusionA (PosAtom s) = VPosSym s
inclusionA (PosConsApp c args) = VConsApp c (map inclusionPat args)

inclusionR :: Refutation -> E
inclusionR (NegAtom s) = ENegSym s
inclusionR (NegConsApp c args) = EConsApp c (map inclusionPat args)

inclusionPat :: Pat -> Term
inclusionPat (PosPat a) = PosTerm (inclusionA a)
inclusionPat (NegPat r) = NegTerm (inclusionR r)

data TypeDef = TypeDef
  { specName :: Symbol
  , specArg :: [(Symbol, Type)]
  } deriving (Show)

-- value-type definition
-- valuedef ::= (value s (x1 t1) ... (xn tn))
type ValueDef = TypeDef

-- computation-type definition
-- compdef ::= (computation s (x1 t1) ... (xn tn))
type CompDef = TypeDef

-- constructor definition
-- consdef ::= (constructor s ((x1 t1) ... (xn tn)) t)
data ConsDef = ConsDef
  { consName :: Symbol
  , consArg :: [(Symbol, Type)]
  , consCod :: Type
  } deriving (Show)

data WeakForm
  = WeakFormHole
  | WeakFormSymbol String
  | WeakFormApp WeakForm
                [WeakForm]
  deriving (Show)

-- form ::= strong-form | (strong-form weak-form1 ... weak-formn)
data Form
  = Form String
         [WeakForm]
  | FormWithRest String
                 [WeakForm]
  deriving (Show)

unifyFormV :: Form -> V -> Either String ([(String, Term)], Maybe [Term])
unifyFormV (Form s ws) (APP (VPosSym (PosSym (S s'))) xs)
  | s /= s' = Left $ "Cannot match " ++ show s ++ " with " ++ show s'
  | length ws /= length xs =
    Left $ "Cannot match " ++ show ws ++ " with " ++ show xs
  | otherwise = do
    ys <- zipWithM unifyEWeakForm ws xs
    return (concat ys, Nothing)
unifyFormV (FormWithRest s ws) (APP (VPosSym (PosSym (S s'))) xs)
  | s /= s' = Left $ "Cannot match " ++ show s ++ " with " ++ show s'
  | length ws > length xs =
    Left $ "Cannot match " ++ show ws ++ " with " ++ show xs
  | otherwise = do
    ys <- zipWithM unifyEWeakForm ws xs
    let rest = drop (length ws) xs
    return (concat ys, Just (map NegTerm rest))
unifyFormV f v = Left $ "Cannot match " ++ show f ++ " with " ++ show v

unifyFormE :: Form -> E -> Either String ([(String, Term)], Maybe [Term])
unifyFormE (Form s ws) (App (ENegSym (NegSym (S s'))) xs)
  | s /= s' = Left $ "Cannot match " ++ show s ++ " with " ++ show s'
  | length ws /= length xs =
    Left $ "Cannot match " ++ show ws ++ " with " ++ show xs
  | otherwise = do
    ys <- zipWithM unifyVWeakForm ws xs
    return (concat ys, Nothing)
unifyFormE (FormWithRest s ws) (App (ENegSym (NegSym (S s'))) xs)
  | s /= s' = Left $ "Cannot match " ++ show s ++ " with " ++ show s'
  | length ws > length xs =
    Left $ "Cannot match " ++ show ws ++ " with " ++ show xs
  | otherwise = do
    ys <- zipWithM unifyVWeakForm ws xs
    let rest = drop (length ws) xs
    return (concat ys, Just (map PosTerm rest))
unifyFormE f v = Left $ "Cannot match " ++ show f ++ " with " ++ show v

unifyVWeakForm :: WeakForm -> V -> Either String [(String, Term)]
unifyVWeakForm WeakFormHole _ = return []
unifyVWeakForm (WeakFormSymbol s) v = return [(s, PosTerm v)]
unifyVWeakForm (WeakFormApp s args) (APP v es) = do
  subst1 <- unifyVWeakForm s v
  subst2 <- zipWithM unifyEWeakForm args es
  return $ subst1 ++ concat subst2
unifyVWeakForm f v = Left $ "Cannot match " ++ show f ++ " against " ++ show v

unifyEWeakForm :: WeakForm -> E -> Either String [(String, Term)]
unifyEWeakForm WeakFormHole _ = return []
unifyEWeakForm (WeakFormSymbol s) e = return [(s, NegTerm e)]
unifyEWeakForm (WeakFormApp s args) (App e vs) = do
  subst1 <- unifyEWeakForm s e
  subst2 <- zipWithM unifyVWeakForm args vs
  return $ subst1 ++ concat subst2
unifyEWeakForm f v = Left $ "Cannot match " ++ show f ++ " against " ++ show v

data Env = Env
  { i :: Int
  , valueTypeEnv :: [ValueDef]
  , compTypeEnv :: [CompDef]
  , consEnv :: [ConsDef]
  , vNotationEnv :: [(String, Form, V)]
  , eNotationEnv :: [(String, Form, E)]
  , reservedEnv :: [String]
  , termEnv :: [Term]
  } deriving (Show)

initialEnv :: Env
initialEnv =
  Env
    { i = 0
    , valueTypeEnv = []
    , compTypeEnv = []
    , consEnv = []
    , vNotationEnv = []
    , eNotationEnv = []
    , reservedEnv = []
    , termEnv = []
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
