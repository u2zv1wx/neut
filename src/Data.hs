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
  deriving (Show)

data PosF n p
  = PosVar Identifier
  | PosConst Identifier
  | PosSigma [(Identifier, p)]
             p
  | PosSigmaIntro [p]
  | PosIndex Identifier
  | PosIndexIntro Index
  | PosDown n
  | PosDownIntro n
  | PosUniv
  | PosBox n
  | PosBoxIntro n
  deriving (Show)

data NegF p n
  = NegPi (Identifier, p)
          n
  | NegPiIntro Identifier
               n
  | NegPiElim n
              p
  | NegSigmaElim p
                 [Identifier]
                 n
  | NegIndexElim p
                 [(Index, n)]
  | NegUpIntro p
  | NegUpElim Identifier
              n
              n
  | NegDownElim p
  | NegBoxElim p
  deriving (Show)

-- type Neut = Cofree NeutF Identifier
$(deriveShow1 ''PosF)

$(deriveShow1 ''NegF)

type PrePos = Cofree (PosF Neg) Identifier

type PreNeg = Cofree (NegF Pos) Identifier

newtype Pos =
  Pos (Cofree (PosF Neg) Identifier)
  deriving (Show)

newtype Neg =
  Neg (Cofree (NegF Pos) Identifier)
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
data ValueF n p
  = ValueVar Identifier
  | ValueConst Identifier
  | ValueSigma [(Identifier, p)]
               p
  | ValueSigmaIntro [p]
  | ValueIndex Identifier
  | ValueIndexIntro Index
  | ValueUniv
  | ValueBox n
  deriving (Show)

-- negative modal normal form
data CompF p n
  = CompPi (Identifier, p)
           n
  | CompPiElim Identifier -- (unbox f) @ x1 @ ... @ xn
               [Identifier]
  | CompSigmaElim p
                  [Identifier]
                  n
  | CompIndexElim p
                  [(Index, n)]
  | CompUpIntro p
  | CompUpElim Identifier
               n
               n
  deriving (Show)

$(deriveShow1 ''ValueF)

$(deriveShow1 ''CompF)

type PreValue = Cofree (ValueF Comp) Identifier

type PreComp = Cofree (CompF Value) Identifier

newtype Value =
  Value (Cofree (ValueF Comp) Identifier)
  deriving (Show)

newtype Comp =
  Comp (Cofree (CompF Value) Identifier)
  deriving (Show)

data Data
  = DataLocal Identifier
  | DataLabel Identifier
  | DataInt32 Int
  | DataStruct [Data]
  deriving (Show)

data Code
  = CodeReturn Data
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

data AsmMeta = AsmMeta
  { asmMetaLive :: [Identifier]
  , asmMetaDef :: [Identifier]
  , asmMetaUse :: [Identifier]
  } deriving (Show)

data AsmData
  = AsmDataReg Identifier
  | AsmDataLabel Identifier
  | AsmDataImmediate Int
  deriving (Show)

data AsmF a
  = AsmReturn Data
  | AsmGetElementPtr Identifier
                     Data
                     (Int, Int)
                     a
  | AsmCall Identifier
            Data
            [Data]
            a
  | AsmCallTail Data
                [Data]
  | AsmBitcast Identifier -- store the result in this register
               Data
               LowType
               LowType -- cast to this type
               a
  | AsmIntToPointer Identifier
                    Data
                    LowType
                    LowType
                    a
  | AsmPointerToInt Identifier
                    Data
                    LowType
                    LowType
                    a
  | AsmSwitch Data
              a
              [(Int, a)]
  | AsmFree Data
            a
  deriving (Show)

$(deriveShow1 ''AsmF)

type Asm = Cofree AsmF AsmMeta

instance (Show a) => Show (IORef a) where
  show a = show (unsafePerformIO (readIORef a))

initialIndexEnv :: [(Identifier, [Identifier])]
initialIndexEnv = [("int", [])]

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
  , constEnv :: [(Identifier, Neut)] -- (name, type)
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
    , indexEnv = initialIndexEnv
    , nameEnv = []
    , typeEnv = []
    , weakTermEnv = []
    , polEnv = []
    , modalEnv = []
    , constEnv = []
    , constraintEnv = []
    , constraintQueue = Q.empty
    , metaMap = []
    , substitution = []
    , caseStack = []
    , univConstraintEnv = []
    , numConstraintEnv = []
    , codeEnv = []
    , asmEnv = []
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

newNameOfPolType :: PrePos -> WithEnv Identifier
newNameOfPolType t = do
  i <- newName
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

lookupConstEnv :: String -> WithEnv (Maybe Neut)
lookupConstEnv s = gets (lookup s . constEnv)

lookupConstEnv' :: String -> WithEnv Neut
lookupConstEnv' s = do
  mt <- gets (lookup s . constEnv)
  env <- get
  case mt of
    Nothing ->
      lift $
      throwE $
      s ++
      " is not found in the const environment. constenv: " ++
      Pr.ppShow (constEnv env)
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

insConstEnv :: Identifier -> Neut -> WithEnv ()
insConstEnv i t = modify (\e -> e {constEnv = (i, t) : constEnv e})

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

addMeta :: AsmF Asm -> WithEnv Asm
addMeta pc = do
  let meta = emptyAsmMeta
  return $ meta :< pc

emptyAsmMeta :: AsmMeta
emptyAsmMeta = AsmMeta {asmMetaLive = [], asmMetaDef = [], asmMetaUse = []}

-- byte size of type
sizeOfType :: Neut -> WithEnv Int
sizeOfType (_ :< NeutVar _) =
  lift $ throwE "Asm.sizeOfType: the type of a type variable is not defined"
sizeOfType (_ :< NeutPi _ _) = return 4
sizeOfType (_ :< NeutSigma xts t2) = do
  let (_, ts) = unzip xts
  is <- mapM sizeOfType ts
  i2 <- sizeOfType t2
  return $ sum is + i2
sizeOfType (_ :< NeutIndex _) = return 4
sizeOfType v = lift $ throwE $ "Asm.sizeOfType: " ++ show v ++ " is not a type"

sizeOfLowType :: LowType -> Int
sizeOfLowType (LowTypeInt _) = 8
sizeOfLowType (LowTypePointer _) = 8
sizeOfLowType (LowTypeStruct ts) = sum $ map sizeOfLowType ts

sizeOf :: Identifier -> WithEnv Int
sizeOf x = do
  t <- lookupTypeEnv' x
  sizeOfType t

intTypeList :: [Identifier]
intTypeList = ["i8", "i16", "i32", "i64"]
