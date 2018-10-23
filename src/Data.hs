{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module Data where

import Prelude hiding (showList)

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
  | IndexFloat Double
  | IndexDefault
  deriving (Show, Eq)

data NeutF a
  = NeutVar Identifier
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
  | NeutConst a -- constant modality
  | NeutConstIntro Identifier
  | NeutConstElim a
  | NeutMu Identifier
           a
  | NeutHole Identifier

type Neut = Cofree NeutF Identifier

$(deriveShow1 ''NeutF)

data LowType
  = LowTypeSignedInt Int
  | LowTypeUnsignedInt Int
  | LowTypeFloat Int
  | LowTypePointer LowType
  | LowTypeFunction [LowType]
                    LowType
  | LowTypeArray Int
                 LowType
  | LowTypeStruct [LowType]
  deriving (Eq)

instance Show LowType where
  show (LowTypeSignedInt i) = "i" ++ show i
  show (LowTypeUnsignedInt i) = "u" ++ show i
  show (LowTypeFloat i) = "f" ++ show i
  show (LowTypePointer t) = show t ++ "*"
  show (LowTypeFunction ts t) = show t ++ " (" ++ showList ts ++ ")"
  show (LowTypeArray i t) = "[" ++ show i ++ " x " ++ show t ++ "]"
  show (LowTypeStruct ts) = "{" ++ showList ts ++ "}"

showList :: Show a => [a] -> String
showList [] = ""
showList [a] = show a
showList (a:as) = show a ++ ", " ++ showList as

data Pos
  = PosVar Identifier
  | PosSigma [(Identifier, Pos)]
             Pos
  | PosSigmaIntro [Pos]
  | PosIndex Identifier
  | PosIndexIntro Index
                  Identifier -- metadata to determine its type
  | PosDown Neg
  | PosDownIntro Neg
  | PosUniv
  | PosBox Neg
  | PosBoxIntro Neg
  | PosConst Pos
  | PosConstIntro Identifier
  | PosArith (Arith, LowType)
             Pos
             Pos
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
  | NegConstElim Pos
  | NegMu Identifier
          Neg
  | NegPrint LowType
             Pos
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
  | ValueSigma [(Identifier, Value)]
               Value
  | ValueSigmaIntro [Value]
  | ValueIndex Identifier
  | ValueIndexIntro Index
                    Identifier
  | ValueUniv
  | ValueBox Comp
  | ValueConst Value
  | ValueConstIntro Identifier
  | ValueArith (Arith, LowType)
               Value
               Value
  deriving (Show)

-- negative modal normal form
data Comp
  = CompPi (Identifier, Value)
           Comp
  | CompPiElimConstElim Identifier -- (unbox f) @ x1 @ ... @ xn
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
  | CompPrint LowType
              Value
  deriving (Show)

data Data
  = DataLocal Identifier
  | DataGlobal Identifier
  | DataInt Int
  | DataFloat16 Double
  | DataFloat32 Double
  | DataFloat64 Double
  | DataStruct [Data]
  | DataArith (Arith, LowType)
              Data
              Data
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
  | CodePrint LowType
              Data
              Code
  deriving (Show)

data AsmData
  = AsmDataLocal Identifier
  | AsmDataGlobal Identifier
  | AsmDataInt Int
  | AsmDataFloat Double

instance Show AsmData where
  show (AsmDataLocal x) = "%" ++ x
  show (AsmDataGlobal x) = "@" ++ x
  show (AsmDataInt i) = show i
  show (AsmDataFloat x) = show x

data Arith
  = ArithAdd
  | ArithSub
  | ArithMul
  | ArithDiv
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
  | AsmArith Identifier
             (Arith, LowType)
             AsmData
             AsmData
             Asm
  | AsmPrint LowType
             AsmData
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

data EnrichedConstraint =
  Enriched PreConstraint
           Constraint
  deriving (Show)

instance Eq EnrichedConstraint where
  (Enriched _ c1) == (Enriched _ c2) = c1 == c2

instance Ord EnrichedConstraint where
  compare (Enriched _ c1) (Enriched _ c2) = compare c1 c2

type Subst = [(Identifier, Neut)]

data Env = Env
  { count :: Int -- to generate fresh symbols
  , notationEnv :: [(Tree, Tree)] -- macro transformers
  , reservedEnv :: [Identifier] -- list of reserved keywords
  , moduleEnv :: [(Identifier, [(Identifier, Neut)])]
  , indexEnv :: [(Identifier, [Identifier])]
  , nameEnv :: [(Identifier, Identifier)] -- used in alpha conversion
  , typeEnv :: [(Identifier, Neut)] -- type environment
  , weakTermEnv :: [(Identifier, Neut)]
  , polEnv :: [(Identifier, Neg)]
  , modalEnv :: [(Identifier, ([Identifier], Comp))]
  -- , modalEnv :: [(Identifier, Value)]
  , constraintEnv :: [PreConstraint]
  , constraintQueue :: Q.MinQueue EnrichedConstraint
  , metaMap :: [(Identifier, PreConstraint)]
  , substitution :: Subst
  , univConstraintEnv :: [(UnivLevel, UnivLevel)]
  , numConstraintEnv :: [Identifier]
  , codeEnv :: [(Identifier, ([Identifier], IORef Code))]
  , asmEnv :: [(Identifier, ([Identifier], Asm))]
  , currentDir :: FilePath
  } deriving (Show)

initialEnv :: FilePath -> Env
initialEnv path =
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
    , moduleEnv = []
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
    , univConstraintEnv = []
    , numConstraintEnv = []
    , currentDir = path
    }

type WithEnv a = StateT Env (ExceptT String IO) a

runWithEnv :: WithEnv a -> Env -> IO (Either String (a, Env))
runWithEnv c env = runExceptT (runStateT c env)

evalWithEnv :: (Show a) => WithEnv a -> Env -> IO (Either String a)
evalWithEnv c env = do
  resultOrErr <- runWithEnv c env
  case resultOrErr of
    Left err -> return $ Left err
    Right (result, _) -> return $ Right result
      -- putStrLn $ Pr.ppShow y
      -- putStrLn $ Pr.ppShow env

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

-- insModalEnv :: Identifier -> Value -> WithEnv ()
-- insModalEnv funName body =
--   modify (\e -> e {modalEnv = (funName, body) : modalEnv e})
insAsmEnv :: Identifier -> [Identifier] -> Asm -> WithEnv ()
insAsmEnv funName args asm =
  modify (\e -> e {asmEnv = (funName, (args, asm)) : asmEnv e})

insIndexEnv :: Identifier -> [Identifier] -> WithEnv ()
insIndexEnv name indexList =
  modify (\e -> e {indexEnv = (name, indexList) : indexEnv e})

lookupKind :: Index -> WithEnv (Maybe Identifier)
lookupKind IndexDefault = return Nothing
lookupKind (IndexInteger _) = return Nothing
lookupKind (IndexFloat _) = return Nothing
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

intLowTypeList :: [LowType]
intLowTypeList = signedIntLowTypeList ++ unsignedIntLowTypeList

signedIntLowTypeList :: [LowType]
signedIntLowTypeList =
  [ LowTypeSignedInt 8
  , LowTypeSignedInt 16
  , LowTypeSignedInt 32
  , LowTypeSignedInt 64
  ]

unsignedIntLowTypeList :: [LowType]
unsignedIntLowTypeList =
  [ LowTypeUnsignedInt 8
  , LowTypeUnsignedInt 16
  , LowTypeUnsignedInt 32
  , LowTypeUnsignedInt 64
  ]

floatLowTypeList :: [LowType]
floatLowTypeList = [LowTypeFloat 16, LowTypeFloat 32, LowTypeFloat 64]
