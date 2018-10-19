{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module Data where

import Control.Comonad

import Control.Comonad.Cofree
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans.Except
import Text.Show.Deriving

import Data.Functor.Classes

import System.IO.Unsafe

import Data.IORef
import Data.List
import Data.Maybe (fromMaybe)

import qualified Data.PQueue.Min as Q

import qualified Text.Show.Pretty as Pr

type Identifier = String

data TreeF a
  = TreeAtom Identifier
  | TreeNode [a]

deriving instance Show a => Show (TreeF a)

deriving instance Functor TreeF

$(deriveShow1 ''TreeF)

type Tree = Cofree TreeF Identifier

data UnivLevel
  = UnivLevelHole Identifier
  | UnivLevelNext UnivLevel
  deriving (Show, Eq)

data Index
  = IndexLabel Identifier
  | IndexInteger Int
  | IndexDefault
  deriving (Show, Eq)

data NeutF a
  = NeutVar Identifier
  | NeutConst Identifier
              a
  | NeutPi (Identifier, a)
           a
  | NeutPiIntro (Identifier, a)
                a
  | NeutPiElim a
               a
  | NeutSigma [(Identifier, a)]
              a
  | NeutSigmaIntro [a]
  | NeutSigmaElim a
                  [Identifier]
                  a
  | NeutBox a
  | NeutBoxIntro a
  | NeutBoxElim a
  | NeutIndex Identifier
  | NeutIndexIntro Index
  | NeutIndexElim a
                  [(Index, a)]
  | NeutUniv UnivLevel
  | NeutMu Identifier
           a
  | NeutHole Identifier

type Neut = Cofree NeutF Identifier

$(deriveShow1 ''NeutF)

deriving instance Eq a => Eq (NeutF a)

data LowType
  = LowTypeInt Int
  | LowTypeStruct [LowType]
  | LowTypePointer LowType
  | LowTypeFunction [LowType]
                    LowType
  deriving (Show)

data Pos
  = PosVar Identifier
  | PosConst Identifier
  | PosSigma [(Identifier, Pos)]
             Pos
  | PosSigmaIntro [Pos]
  | PosIndex Identifier
  | PosIndexIntro Index
  | PosDown Neg
  | PosDownIntro Neg
  | PosUniv
  | PosBox Neg
  | PosBoxIntro Neg
  deriving (Show)

data Neg
  = NegPi (Identifier, Pos)
          Neg
  | NegPiIntro Identifier
               Neg
  | NegPiElim Neg
              Pos
  | NegSigmaElim Pos
                 [Identifier]
                 Neg
  | NegIndexElim Pos
                 [(Index, Neg)]
  | NegUpIntro Pos
  | NegUpElim Identifier
              Neg
              Neg
  | NegDownElim Pos
  | NegBoxElim Pos
  | NegMu Identifier
          Neg
  deriving (Show)

-- A polarize term is in *modal-normal form* if the following two conditions are true:
-- (1) for every application `e @ v1 @ ... @ vn`,
--   - e == (unbox x) for some variable x,
--   - vi == xi for some variable x,
-- (2) the term doesn't contain any thunk/force.
-- (3) for every unboxing `(unbox v)`, v == x for some variable x.
--
-- Note that there exists a type isomorphism:
--  Down N === Sigma (P : Type). Box (P -> N) * P.
-- We emploty this type isomorphism in `Modal.hs` to eliminate all the thunk/forces.
--
-- positive modal normal form
data Value
  = ValueVar Identifier
  | ValueConst Identifier
  | ValueSigma [(Identifier, Value)]
               Value
  | ValueSigmaIntro [Value]
  | ValueIndex Identifier
  | ValueIndexIntro Index
  | ValueUniv
  | ValueBox Comp
  deriving (Show)

-- negative modal normal form
data Comp
  = CompPi (Identifier, Value)
           Comp
  | CompPiElim Identifier -- (unbox f) @ x1 @ ... @ xn
               [Identifier]
  | CompSigmaElim Value
                  [Identifier]
                  Comp
  | CompIndexElim Value
                  [(Index, Comp)]
  | CompUpIntro Value
  | CompUpElim Identifier
               Comp
               Comp
  deriving (Show)

data Data
  = DataLocal Identifier
  | DataGlobal Identifier
  | DataInt32 Int
  | DataStruct [Data]
  deriving (Show)

data Code
  = CodeReturn Data
  | CodeLet Identifier
            Data
            Code
  | CodeCall Identifier -- the register that stores the result of a function call (type: P)
             Data -- the name of the function (type: Box (P1 -> ... -> Pn -> ↑P))
             [Data] -- arguments (type : [P1, ..., Pn])
             Code -- continuation
  | CodeCallTail Data -- the name of the function (type: Box (P1 -> ... -> Pn -> ↑P))
                 [Data] -- arguments (type : [P1, ..., Pn])
  | CodeSwitch Data
               [(Index, Code)]
  | CodeExtractValue Identifier -- destination
                     Data -- base pointer
                     (Int, Int) -- (i, n) ... index i in [1 ... n]
                     Code -- continuation
  | CodeFree Data
             Code
  deriving (Show)

data AsmData
  = AsmDataLocal Identifier
  | AsmDataGlobal Identifier
  | AsmDataInt32 Int
  deriving (Show)

data Asm
  = AsmReturn AsmData
  | AsmGetElementPtr Identifier
                     AsmData
                     (Int, Int)
                     Asm
  | AsmCall Identifier
            AsmData
            [AsmData]
            Asm
  | AsmCallTail AsmData
                [AsmData]
  | AsmSwitch AsmData
              Asm
              [(Int, Asm)]
  | AsmBitcast Identifier -- store the result in this register
               AsmData
               LowType
               LowType -- cast to this type
               Asm
  | AsmIntToPointer Identifier
                    AsmData
                    LowType
                    LowType
                    Asm
  | AsmPointerToInt Identifier
                    AsmData
                    LowType
                    LowType
                    Asm
  | AsmLoad Identifier
            AsmData
            Asm
  | AsmStore (AsmData, LowType)
             (AsmData, LowType)
             Asm
  | AsmAlloc Identifier
             [LowType]
             Asm
  | AsmFree AsmData
            Asm
  deriving (Show)

instance (Show a) => Show (IORef a) where
  show a = show (unsafePerformIO (readIORef a))

type Context = [Identifier]

-- (Gamma, e1, e2, t)  ==  Gamma |- e1 = e2 : t
type PreConstraint = (Context, Neut, Neut, Neut)

data WeakConstraint
  = ConstraintPattern Identifier
                      [Identifier]
                      Neut
  | ConstraintBeta Identifier
                   Neut
  | ConstraintDelta Identifier
                    [Neut]
                    [Neut]
  | ConstraintQuasiPattern Identifier
                           [Identifier]
                           Neut
  | ConstraintFlexRigid Identifier
                        [Neut]
                        Neut
  | ConstraintFlexFlex Identifier
                       [Neut]
                       Identifier
                       [Neut]
  deriving (Show)

data Constraint =
  Constraint Context
             WeakConstraint
             Neut
  deriving (Show)

constraintToInt :: WeakConstraint -> Int
constraintToInt ConstraintPattern {} = 0
constraintToInt ConstraintDelta {} = 1
constraintToInt ConstraintBeta {} = 2
constraintToInt ConstraintQuasiPattern {} = 3
constraintToInt ConstraintFlexRigid {} = 4
constraintToInt ConstraintFlexFlex {} = 5

instance Eq WeakConstraint where
  c1 == c2 = constraintToInt c1 == constraintToInt c2

instance Ord WeakConstraint where
  compare c1 c2 = compare (constraintToInt c1) (constraintToInt c2)

instance Eq Constraint where
  (Constraint _ c1 _) == (Constraint _ c2 _) = c1 == c2

instance Ord Constraint where
  compare (Constraint _ c1 _) (Constraint _ c2 _) = compare c1 c2

type Subst = [(Identifier, Neut)]

data Justification
  = Asserted Identifier
  | Assumption Identifier
  | Join [Justification]
  deriving (Show)

data Case = Case
  { constraintQueueSnapshot :: Q.MinQueue Constraint
  , metaMapSnapshot :: [(Identifier, PreConstraint)]
  , substitutionSnapshot :: Subst
  , caseJustification :: Justification
  , savedJustification :: Justification
  , alternatives :: [[PreConstraint]]
  } deriving (Show)

data Env = Env
  { count :: Int -- to generate fresh symbols
  , notationEnv :: [(Tree, Tree)] -- macro transformers
  , reservedEnv :: [Identifier] -- list of reserved keywords
  , indexEnv :: [(Identifier, [Identifier])]
  , nameEnv :: [(Identifier, Identifier)] -- used in alpha conversion
  , typeEnv :: [(Identifier, Neut)] -- type environment
  , weakTermEnv :: [(Identifier, Neut)]
  , polEnv :: [(Identifier, Neg)]
  , modalEnv :: [(Identifier, ([Identifier], Comp))]
  , constraintEnv :: [PreConstraint]
  , constraintQueue :: Q.MinQueue Constraint
  , metaMap :: [(Identifier, PreConstraint)]
  , substitution :: Subst
  , caseStack :: [Case]
  , univConstraintEnv :: [(UnivLevel, UnivLevel)]
  , numConstraintEnv :: [Identifier]
  , codeEnv :: [(Identifier, ([Identifier], IORef Code))]
  , asmEnv :: [(Identifier, ([Identifier], Asm))]
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
    , indexEnv = []
    , nameEnv = []
    , typeEnv = []
    , weakTermEnv = []
    , polEnv = []
    , modalEnv = []
    , codeEnv = []
    , asmEnv = []
    , constraintEnv = []
    , constraintQueue = Q.empty
    , metaMap = []
    , substitution = []
    , caseStack = []
    , univConstraintEnv = []
    , numConstraintEnv = []
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

newNameOfType :: Neut -> WithEnv Identifier
newNameOfType t = do
  i <- newName
  insTypeEnv i t
  return i

constNameWith :: Identifier -> WithEnv ()
constNameWith s = modify (\e -> e {nameEnv = (s, s) : nameEnv e})

lookupTypeEnv :: String -> WithEnv (Maybe Neut)
lookupTypeEnv s = gets (lookup s . typeEnv)

lookupTypeEnv' :: String -> WithEnv Neut
lookupTypeEnv' s = do
  mt <- gets (lookup s . typeEnv)
  case mt of
    Nothing -> lift $ throwE $ s ++ " is not found in the type environment."
    Just t -> return t

insNameEnv :: Identifier -> Identifier -> WithEnv ()
insNameEnv from to = modify (\e -> e {nameEnv = (from, to) : nameEnv e})

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

lookupCodeEnv :: Identifier -> WithEnv ([Identifier], IORef Code)
lookupCodeEnv funName = do
  env <- get
  case lookup funName (codeEnv env) of
    Just (args, body) -> return (args, body)
    Nothing -> lift $ throwE $ "no such code: " ++ show funName

insTypeEnv :: Identifier -> Neut -> WithEnv ()
insTypeEnv i t = modify (\e -> e {typeEnv = (i, t) : typeEnv e})

insNumConstraintEnv :: Identifier -> WithEnv ()
insNumConstraintEnv x =
  modify (\e -> e {numConstraintEnv = x : numConstraintEnv e})

insWeakTermEnv :: Identifier -> Neut -> WithEnv ()
insWeakTermEnv i t = modify (\e -> e {weakTermEnv = weakTermEnv e ++ [(i, t)]})

lookupWeakTermEnv :: Identifier -> WithEnv Neut
lookupWeakTermEnv funName = do
  env <- get
  case lookup funName (weakTermEnv env) of
    Just body -> return body
    Nothing -> lift $ throwE $ "no such weakterm: " ++ show funName

-- funName : Box (P1 -> ... -> Pn -> N)
-- arg_i : Pi
-- body : N
insCodeEnv :: Identifier -> [Identifier] -> Code -> WithEnv ()
insCodeEnv funName args body = do
  codeRef <- liftIO $ newIORef body
  modify (\e -> e {codeEnv = (funName, (args, codeRef)) : codeEnv e})

insPolEnv :: Identifier -> Neg -> WithEnv ()
insPolEnv name body = modify (\e -> e {polEnv = (name, body) : polEnv e})

insModalEnv :: Identifier -> [Identifier] -> Comp -> WithEnv ()
insModalEnv funName args body =
  modify (\e -> e {modalEnv = (funName, (args, body)) : modalEnv e})

insAsmEnv :: Identifier -> [Identifier] -> Asm -> WithEnv ()
insAsmEnv funName args asm =
  modify (\e -> e {asmEnv = (funName, (args, asm)) : asmEnv e})

insIndexEnv :: Identifier -> [Identifier] -> WithEnv ()
insIndexEnv name indexList =
  modify (\e -> e {indexEnv = (name, indexList) : indexEnv e})

lookupKind :: Index -> WithEnv (Maybe Identifier)
lookupKind IndexDefault = return Nothing
lookupKind (IndexInteger _) = return Nothing
lookupKind (IndexLabel name) = do
  env <- get
  lookupKind' name $ indexEnv env

lookupKind' ::
     Identifier -> [(Identifier, [Identifier])] -> WithEnv (Maybe Identifier)
lookupKind' _ [] = return Nothing
lookupKind' i ((j, ls):xs) =
  if i `elem` ls
    then return $ Just j
    else lookupKind' i xs

lookupIndexSet :: Identifier -> WithEnv [Identifier]
lookupIndexSet name = do
  env <- get
  lookupIndexSet' name $ indexEnv env

lookupIndexSet' ::
     Identifier -> [(Identifier, [Identifier])] -> WithEnv [Identifier]
lookupIndexSet' name [] = lift $ throwE $ "no such index defined: " ++ show name
lookupIndexSet' name ((_, ls):xs) =
  if name `elem` ls
    then return ls
    else lookupIndexSet' name xs

indexToInt :: Index -> WithEnv Int
indexToInt IndexDefault = return 0
indexToInt (IndexInteger i) = return i
indexToInt (IndexLabel name) = do
  set <- lookupIndexSet name
  case elemIndex name set of
    Just i -> return i
    Nothing -> lift $ throwE $ "no such index defined: " ++ show name

isDefinedIndex :: Identifier -> WithEnv Bool
isDefinedIndex name = do
  env <- get
  let labelList = join $ map snd $ indexEnv env
  return $ name `elem` labelList

isDefinedIndexName :: Identifier -> WithEnv Bool
isDefinedIndexName name = do
  env <- get
  let indexNameList = map fst $ indexEnv env
  return $ name `elem` indexNameList

insConstraintEnv :: Context -> Neut -> Neut -> Neut -> WithEnv ()
insConstraintEnv ctx t1 t2 t =
  modify (\e -> e {constraintEnv = (ctx, t1, t2, t) : constraintEnv e})

insUnivConstraintEnv :: UnivLevel -> UnivLevel -> WithEnv ()
insUnivConstraintEnv t1 t2 =
  modify (\e -> e {univConstraintEnv = (t1, t2) : univConstraintEnv e})

wrapArg :: Identifier -> WithEnv Neut
wrapArg i = do
  t <- lookupTypeEnv' i
  meta <- newNameWith "meta"
  insTypeEnv meta t
  return $ meta :< NeutVar i

wrap :: f (Cofree f Identifier) -> WithEnv (Cofree f Identifier)
wrap a = do
  meta <- newNameWith "meta"
  return $ meta :< a

wrapType :: NeutF Neut -> WithEnv Neut
wrapType t = do
  meta <- newNameWith "meta"
  hole <- newName
  u <- wrap $ NeutUniv (UnivLevelHole hole)
  insTypeEnv meta u
  return $ meta :< t

wrapTypeWithUniv :: Neut -> NeutF Neut -> WithEnv Neut
wrapTypeWithUniv univ t = do
  meta <- newNameWith "meta"
  insTypeEnv meta univ
  return $ meta :< t

intTypeList :: [Identifier]
intTypeList = ["i8", "i16", "i32", "i64"]
