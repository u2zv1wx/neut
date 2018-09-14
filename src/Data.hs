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

import           Data.Functor.Classes

import           System.IO.Unsafe

import           Data.List

import qualified Text.Show.Pretty           as Pr

type Identifier = String

data TreeF a
  = TreeAtom Identifier
  | TreeNode [a]

deriving instance Show a => Show (TreeF a)

deriving instance Functor TreeF

$(deriveShow1 ''TreeF)

type Tree = Cofree TreeF Identifier

data NeutF a
  = NeutVar Identifier
  | NeutForall (Identifier, a) -- forall-form
               a
  | NeutLam Identifier -- forall-intro
            a
  | NeutApp a -- forall-elim
            a
  | NeutExists (Identifier, a) -- exists-form
               a
  | NeutPair a -- exists-intro
             a
  | NeutCase a
             (Identifier, Identifier) -- exists-elim
             a
  | NeutTop -- top-form
  | NeutUnit -- top-intro
  | NeutBottom -- bottom-form
  | NeutAbort a -- bottom-elim
  | NeutUniv
  | NeutMu Identifier -- recursion
           a
  | NeutHole Identifier

type Neut = Cofree NeutF Identifier

$(deriveShow1 ''NeutF)

data PosF c v
  = PosVar Identifier
  | PosPair v -- exists-intro
            v
  | PosUnit -- top-intro
  | PosThunk c -- down-intro
  | PosTypeForall (Identifier, v) -- forall-form
                  v
  | PosTypeExists (Identifier, v) -- exists-form
                  v
  | PosTypeTop -- top-form
  | PosTypeBottom -- bottom-form
  | PosTypeUniv

data NegF v c
  = NegLam Identifier -- forall-intro
           c
  | NegApp c -- forall-elim
           [Identifier]
  | NegCase v
            (Identifier, Identifier) -- exists-elim
            c
  | NegAbort c -- bottom-elim
  | NegReturn v -- up-intro
  | NegBind Identifier -- up-elim
            c
            c
  | NegForce Identifier -- down-elim
  | NegMu Identifier -- recursion
          c

$(deriveShow1 ''PosF)

$(deriveShow1 ''NegF)

type PrePos = Cofree (PosF Neg) Identifier

type PreNeg = Cofree (NegF Pos) Identifier

newtype Pos =
  Pos PrePos
  deriving (Show)

newtype Neg =
  Neg PreNeg
  deriving (Show)

data Term
  = Value Pos
  | Comp Neg
  deriving (Show)

type Index = [Int]

data Data
  = DataLocal Identifier
  | DataGlobal Identifier
  | DataElemAtIndex Identifier -- subvalue of an inductive value
                    Index
  | DataInt32 Int
  deriving (Show)

type ConstructorName = Identifier

type ConstructorId = Int

type TargetLabel = Identifier

type Branch = (ConstructorName, ConstructorId, TargetLabel, Code)

type Address = Identifier

type DefaultBranch = (TargetLabel, Code)

type DefaultAsmBranch = (TargetLabel, [Asm])

type AsmBranch = (ConstructorName, ConstructorId, TargetLabel, [Asm])

data Code
  = CodeReturn Data
  | CodeLet Identifier -- bind (we also use this to represent application)
            Data
            Code
  | CodeSwitch Identifier -- branching in pattern-matching (elimination of inductive type)
               DefaultBranch
               [Branch]
  | CodeCall Identifier -- the register that stores the result of a function call
             Identifier -- the name of the function
             [Data] -- arguments
             Code -- continuation
  | CodeLoad Data
  deriving (Show)

data AsmData
  = AsmDataLocal Identifier
  | AsmDataGlobal Identifier
  | AsmDataInt32 Int
  deriving (Show)

data Asm
  = AsmReturn Identifier
  | AsmLet Identifier
           AsmOperation
  | AsmStore AsmData -- source data
             Identifier -- destination register
  | AsmSwitch Identifier
              DefaultAsmBranch
              [AsmBranch]
  deriving (Show)

data AsmOperation
  = AsmAlloc Term
  | AsmLoad Identifier -- source register
  | AsmGetElemPointer Identifier -- base register
                      Index -- index
  | AsmCall Identifier
            [Identifier]
  | AsmBitcast Term
               Identifier
               Term
  deriving (Show)

data Env = Env
  { count         :: Int -- to generate fresh symbols
  , notationEnv   :: [(Tree, Tree)] -- macro transformers
  , reservedEnv   :: [Identifier] -- list of reserved keywords
  , nameEnv       :: [(Identifier, Identifier)] -- used in alpha conversion
  , typeEnv       :: [(Identifier, Neut)] -- type environment
  , constraintEnv :: [(Neut, Neut)] -- used in type inference
  , codeEnv       :: [(Identifier, ([Identifier], Code))]
  } deriving (Show)

initialEnv :: Env
initialEnv =
  Env
    { count = 0
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
    , typeEnv = []
    , constraintEnv = []
    , codeEnv = []
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
  return $ "." ++ show i

newNameWith :: Identifier -> WithEnv Identifier
newNameWith s = do
  i <- newName
  let s' = s ++ i
  modify (\e -> e {nameEnv = (s, s') : nameEnv e})
  return s'

lookupTypeEnv :: String -> WithEnv (Maybe Neut)
lookupTypeEnv s = gets (lookup s . typeEnv)

lookupTypeEnv' :: String -> WithEnv Neut
lookupTypeEnv' s = do
  mt <- gets (lookup s . typeEnv)
  env <- get
  case mt of
    Nothing ->
      lift $
      throwE $
      s ++
      " is not found in the type environment. typeenv: " ++
      Pr.ppShow (typeEnv env)
    Just t -> return t

lookupNameEnv :: String -> WithEnv String
lookupNameEnv s = do
  env <- get
  case lookup s (nameEnv env) of
    Just s' -> return s'
    Nothing -> lift $ throwE $ "undefined variable: " ++ show s

lookupNameEnv' :: String -> WithEnv String
lookupNameEnv' s = do
  env <- get
  case lookup s (nameEnv env) of
    Just s' -> return s'
    Nothing -> newNameWith s

lookupCodeEnv :: Identifier -> WithEnv ([Identifier], Code)
lookupCodeEnv funName = do
  env <- get
  case lookup funName (codeEnv env) of
    Just (args, body) -> return (args, body)
    Nothing           -> lift $ throwE $ "no such code: " ++ show funName

insTypeEnv :: Identifier -> Neut -> WithEnv ()
insTypeEnv i t = modify (\e -> e {typeEnv = (i, t) : typeEnv e})

insCodeEnv :: Identifier -> [Identifier] -> Code -> WithEnv ()
insCodeEnv funName args body =
  modify (\e -> e {codeEnv = (funName, (args, body)) : codeEnv e})

insConstraintEnv :: Neut -> Neut -> WithEnv ()
insConstraintEnv t1 t2 =
  modify (\e -> e {constraintEnv = (t1, t2) : constraintEnv e})

local :: WithEnv a -> WithEnv a
local p = do
  env <- get
  x <- p
  modify (\e -> env {count = count e})
  return x

recurM :: (Monad m) => (Tree -> m Tree) -> Tree -> m Tree
recurM f (meta :< TreeAtom s) = f (meta :< TreeAtom s)
recurM f (meta :< TreeNode tis) = do
  tis' <- mapM (recurM f) tis
  f (meta :< TreeNode tis')

foldML ::
     (Cofree f Identifier -> a -> f (Cofree f Identifier))
  -> Cofree f Identifier
  -> [a]
  -> StateT Env (ExceptT String IO) (Cofree f Identifier)
foldML _ e [] = return e
foldML f e (t:ts) = do
  let tmp = f e t
  i <- newName
  foldML f (i :< tmp) ts

foldMR ::
     (a -> Cofree f Identifier -> f (Cofree f Identifier))
  -> Cofree f Identifier
  -> [a]
  -> StateT Env (ExceptT String IO) (Cofree f Identifier)
foldMR _ e [] = return e
foldMR f e (t:ts) = do
  tmp <- foldMR f e ts
  let x = f t tmp
  i <- newName
  return $ i :< x

letSeq :: [Identifier] -> [Data] -> Code -> WithEnv Code
letSeq [] [] code = return code
letSeq (i:is) (d:ds) code = do
  tmp <- letSeq is ds code
  return $ CodeLet i d tmp
letSeq _ _ _ = error "Virtual.letSeq: invalid arguments"

swap :: Int -> Int -> [a] -> [a]
swap i j xs = replaceNth j (xs !! i) (replaceNth i (xs !! j) xs)

replaceNth :: Int -> a -> [a] -> [a]
replaceNth _ _ [] = []
replaceNth n newVal (x:xs)
  | n == 0 = newVal : xs
  | otherwise = x : replaceNth (n - 1) newVal xs

appFold :: Neut -> [Neut] -> WithEnv Neut
appFold e [] = return e
appFold e@(i :< _) (term:ts) = do
  t <- lookupTypeEnv' i
  case t of
    _ :< NeutForall _ tcod -> do
      meta <- newNameWith "meta"
      insTypeEnv meta tcod
      appFold (meta :< NeutApp e term) ts
    _ -> error "Lift.appFold"

constructFormalArgs :: [Identifier] -> WithEnv [Identifier]
constructFormalArgs [] = return []
constructFormalArgs (ident:is) = do
  varType <- lookupTypeEnv' ident
  formalArg <- newNameWith "arg"
  insTypeEnv formalArg varType
  args <- constructFormalArgs is
  return $ formalArg : args

wrapArg :: Identifier -> WithEnv Neut
wrapArg i = do
  t <- lookupTypeEnv' i
  meta <- newNameWith "meta"
  insTypeEnv meta t
  return $ meta :< NeutVar i

bindFormalArgs :: [Identifier] -> Neut -> WithEnv Neut
bindFormalArgs [] terminal = return terminal
bindFormalArgs (arg:xs) c@(metaLam :< _) = do
  tLam <- lookupTypeEnv' metaLam
  tArg <- lookupTypeEnv' arg
  tmp <- bindFormalArgs xs c
  meta <- newNameWith "meta"
  univMeta <- newNameWith "meta"
  insTypeEnv univMeta (univMeta :< NeutUniv)
  insTypeEnv meta (univMeta :< NeutForall (arg, tArg) tLam)
  return $ meta :< NeutLam arg tmp

forallArgs :: Neut -> (Neut, [(Identifier, Neut, Identifier)])
forallArgs (meta :< NeutForall (i, vt) t) = do
  let (body, xs) = forallArgs t
  (body, (i, vt, meta) : xs)
forallArgs body = (body, [])

coForallArgs :: (Neut, [(Identifier, Neut, Identifier)]) -> Neut
coForallArgs (t, []) = t
coForallArgs (t, (i, tdom, meta):ts) =
  coForallArgs (meta :< NeutForall (i, tdom) t, ts)

funAndArgs :: Neut -> WithEnv (Neut, [(Identifier, Neut)])
funAndArgs (i :< NeutApp e v) = do
  (fun, xs) <- funAndArgs e
  return (fun, (i, v) : xs)
funAndArgs c = return (c, [])

coFunAndArgs :: (Neut, [(Identifier, Neut)]) -> Neut
coFunAndArgs (term, [])        = term
coFunAndArgs (term, (i, v):xs) = coFunAndArgs (i :< NeutApp term v, xs)

var :: Neut -> [Identifier]
var (_ :< NeutVar s) = [s]
var (_ :< NeutForall (i, tdom) tcod) = var tdom ++ filter (/= i) (var tcod)
var (_ :< NeutLam s e) = filter (/= s) $ var e
var (_ :< NeutApp e v) = var e ++ var v
var (_ :< NeutExists (i, tdom) tcod) = var tdom ++ filter (/= i) (var tcod)
var (_ :< NeutPair v1 v2) = var v1 ++ var v2
var (_ :< NeutCase e1 (x, y) e2) =
  var e1 ++ filter (\s -> s /= x && s /= y) (var e2)
var (_ :< NeutTop) = []
var (_ :< NeutUnit) = []
var (_ :< NeutBottom) = []
var (_ :< NeutAbort e) = var e
var (_ :< NeutUniv) = []
var (_ :< NeutMu s e) = filter (/= s) (var e)
var (_ :< NeutHole _) = []
