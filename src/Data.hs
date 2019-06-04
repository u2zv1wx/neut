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

import qualified Data.Map.Strict as Map

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

-- type IndexOrVar = Either Index Identifier
data Arith
  = ArithAdd
  | ArithSub
  | ArithMul
  | ArithDiv
  deriving (Show)

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

voidPtr :: LowType
voidPtr = LowTypePointer $ LowTypeSignedInt 8

data NeutF a
  = NeutVar Identifier
  | NeutConst Identifier
  | NeutPi (Identifier, a)
           a
  | NeutPiIntro (Identifier, a)
                a
  | NeutPiElim a
               a
  | NeutSigma [(Identifier, a)]
  | NeutSigmaIntro [a]
  | NeutSigmaElim a
                  [Identifier]
                  a
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

var :: Neut -> [Identifier]
var e = fst $ varAndHole e

varAndHole :: Neut -> ([Identifier], [Identifier])
varAndHole (_ :< NeutVar s) = ([s], [])
varAndHole (_ :< NeutPi (x, tdom) tcod) = do
  let vs1 = varAndHole tdom
  let (vs21, vs22) = varAndHole tcod
  let vs2 = (filter (/= x) vs21, vs22)
  pairwiseConcat [vs1, vs2]
varAndHole (_ :< NeutPiIntro (x, _) e) = do
  let (vs1, vs2) = varAndHole e
  (filter (/= x) vs1, vs2)
varAndHole (_ :< NeutPiElim e1 e2) =
  pairwiseConcat [varAndHole e1, varAndHole e2]
varAndHole (_ :< NeutSigma xts) = varAndHoleSigma xts
varAndHole (_ :< NeutSigmaIntro es) = pairwiseConcat $ map varAndHole es
varAndHole (_ :< NeutSigmaElim e1 xs e2) = do
  let vs1 = varAndHole e1
  let (vs21, vs22) = varAndHole e2
  let vs2 = (filter (`notElem` xs) vs21, vs22)
  pairwiseConcat [vs1, vs2]
varAndHole (_ :< NeutIndex _) = ([], [])
varAndHole (_ :< NeutIndexIntro _) = ([], [])
varAndHole (_ :< NeutIndexElim e branchList) = do
  let vs1 = varAndHole e
  vss <- forM branchList $ \(_, body) -> return $ varAndHole body
  pairwiseConcat (vs1 : vss)
varAndHole (_ :< NeutConst _) = ([], [])
varAndHole (_ :< NeutUniv _) = ([], [])
varAndHole (_ :< NeutMu x e) = do
  let (vs1, vs2) = varAndHole e
  (filter (/= x) vs1, vs2)
varAndHole (_ :< NeutHole x) = ([], [x])

varAndHoleSigma :: [(Identifier, Neut)] -> ([Identifier], [Identifier])
varAndHoleSigma [] = ([], [])
varAndHoleSigma ((x, t):xts) = do
  let vs1 = varAndHole t
  let (vs21, vs22) = varAndHoleSigma xts
  let vs2 = (filter (/= x) vs21, vs22)
  pairwiseConcat [vs1, vs2]

pairwiseConcat :: [([a], [b])] -> ([a], [b])
pairwiseConcat [] = ([], [])
pairwiseConcat ((xs, ys):rest) = do
  let (xs', ys') = pairwiseConcat rest
  (xs ++ xs', ys ++ ys')

data Term
  = TermVar Identifier
  | TermConst Identifier
  | TermPiIntro Identifier
                Term
  | TermPiElim Term
               Term
  | TermSigmaIntro [Term]
  | TermSigmaElim Term
                  [Identifier]
                  Term
  | TermIndexIntro Index
                   LowType
  | TermIndexElim Term
                  [(Index, Term)]
  | TermMu Identifier
           Term
  deriving (Show)

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

data Constant
  = ConstantArith LowType
                  Arith
  | ConstantPrint LowType
  deriving (Show)

data Pos
  = PosVar Identifier
  | PosConst Identifier
  | PosSigmaIntro [Pos]
  | PosIndexIntro Index
                  LowType
  | PosDownIntro Neg
  deriving (Show)

data Neg
  = NegPiIntro Identifier
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
  | NegConstElim Constant
                 [Pos]
  deriving (Show)

-- positive modal normal form
data Value
  = ValueVar Identifier
  | ValueConst Identifier
  | ValueSigmaIntro [Value]
  | ValueIndexIntro Index
                    LowType
  deriving (Show)

-- negative modal normal form
data Comp
  = CompPiElimBoxElim Value -- (force f) @ x1 @ ... @ xn
                      [Value]
  | CompConstElim Constant
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

data LLVMData
  = LLVMDataLocal Identifier
  | LLVMDataGlobal Identifier
  | LLVMDataInt Int
  | LLVMDataFloat Double

instance Show LLVMData where
  show (LLVMDataLocal x) = "%" ++ x
  show (LLVMDataGlobal x) = "@" ++ x
  show (LLVMDataInt i) = show i
  show (LLVMDataFloat x) = show x

data LLVM
  = LLVMCall LLVMData -- PiElimDownElim
             [LLVMData]
  | LLVMSwitch LLVMData -- IndexElim
               LLVM
               [(Int, LLVM)]
  | LLVMReturn LLVMData -- UpIntro
  | LLVMLet Identifier -- UpElim
            LLVM
            LLVM
  | LLVMGetElementPtr LLVMData
                      (Int, Int) -- (index, length)
  | LLVMBitcast LLVMData
                LowType
                LowType -- cast to this type
  | LLVMIntToPointer LLVMData
                     LowType
                     LowType
  | LLVMPointerToInt LLVMData
                     LowType
                     LowType
  | LLVMLoad LLVMData
  | LLVMStore (LLVMData, LowType)
              (LLVMData, LowType)
  | LLVMAlloc [LowType]
  | LLVMFree LLVMData
  | LLVMArith (Arith, LowType)
              LLVMData
              LLVMData
  | LLVMPrint LowType
              LLVMData
  deriving (Show)

instance (Show a) => Show (IORef a) where
  show a = show (unsafePerformIO (readIORef a))

type Context = [(Identifier, Neut)]

type PreConstraint = (Neut, Neut)

data Constraint
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

constraintToInt :: Constraint -> Int
constraintToInt ConstraintPattern {} = 0
constraintToInt ConstraintDelta {} = 1
constraintToInt ConstraintBeta {} = 2
constraintToInt ConstraintQuasiPattern {} = 3
constraintToInt ConstraintFlexRigid {} = 4
constraintToInt ConstraintFlexFlex {} = 5

instance Eq Constraint where
  c1 == c2 = constraintToInt c1 == constraintToInt c2

instance Ord Constraint where
  compare c1 c2 = compare (constraintToInt c1) (constraintToInt c2)

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
  , constantEnv :: [Identifier]
  , moduleEnv :: [(Identifier, [(Identifier, Neut)])]
  , indexEnv :: [(Identifier, [Identifier])]
  , nameEnv :: [(Identifier, Identifier)] -- used in alpha conversion
  , typeEnv :: Map.Map Identifier Neut
  , constraintEnv :: [PreConstraint] -- for type inference
  , constraintQueue :: Q.MinQueue EnrichedConstraint -- for (dependent) type inference
  , substitution :: Subst -- for (dependent) type inference
  , univConstraintEnv :: [(UnivLevel, UnivLevel)]
  , currentDir :: FilePath
  , polEnv :: [(Identifier, Neg)] -- x ~> box.intro e
  , modalEnv :: [(Identifier, ([Identifier], Comp))] -- x ~> box (lam (x1 ... xn) e))
  , llvmEnv :: [(Identifier, ([Identifier], LLVM))] -- x ~> box (lam (x1 ... xn) e)
  } deriving (Show)

initialEnv :: FilePath -> Env
initialEnv path =
  Env
    { count = 0
    , notationEnv = []
    , reservedEnv = []
    , constantEnv = []
    , moduleEnv = []
    , indexEnv = []
    , nameEnv = []
    , typeEnv = Map.empty
    , polEnv = []
    , modalEnv = []
    , llvmEnv = []
    , constraintEnv = []
    , constraintQueue = Q.empty
    , substitution = []
    , univConstraintEnv = []
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

newName1 :: Identifier -> Neut -> WithEnv Identifier
newName1 baseName t = do
  i <- newNameWith baseName
  insTypeEnv i t
  return i

constNameWith :: Identifier -> WithEnv ()
constNameWith s = modify (\e -> e {nameEnv = (s, s) : nameEnv e})

lookupTypeEnv :: String -> WithEnv (Maybe Neut)
lookupTypeEnv s = gets (Map.lookup s . typeEnv)

lookupTypeEnv' :: String -> WithEnv Neut
lookupTypeEnv' s = do
  mt <- gets (Map.lookup s . typeEnv)
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

lookupNameEnv'' :: String -> WithEnv (Maybe String)
lookupNameEnv'' s = do
  env <- get
  case lookup s (nameEnv env) of
    Just s' -> return $ Just s'
    Nothing -> return Nothing

insTypeEnv :: Identifier -> Neut -> WithEnv ()
insTypeEnv i t = modify (\e -> e {typeEnv = Map.insert i t (typeEnv e)})

insTypeEnv1 :: Identifier -> Neut -> WithEnv ()
insTypeEnv1 i t = do
  tenv <- gets typeEnv
  let ts = Map.elems $ Map.filterWithKey (\j _ -> i == j) tenv
  forM_ ts $ \t' -> insConstraintEnv t t'
  modify (\e -> e {typeEnv = Map.insert i t (typeEnv e)})

insPolEnv :: Identifier -> Neg -> WithEnv ()
insPolEnv name body = modify (\e -> e {polEnv = (name, body) : polEnv e})

insModalEnv :: Identifier -> [Identifier] -> Comp -> WithEnv ()
insModalEnv funName args body =
  modify (\e -> e {modalEnv = (funName, (args, body)) : modalEnv e})

insLLVMEnv :: Identifier -> [Identifier] -> LLVM -> WithEnv ()
insLLVMEnv funName args llvm =
  modify (\e -> e {llvmEnv = (funName, (args, llvm)) : llvmEnv e})

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

insConstraintEnv :: Neut -> Neut -> WithEnv ()
insConstraintEnv t1 t2 =
  modify (\e -> e {constraintEnv = (t1, t2) : constraintEnv e})

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
  [ LowTypeSignedInt 1
  , LowTypeSignedInt 2
  , LowTypeSignedInt 4
  , LowTypeSignedInt 8
  , LowTypeSignedInt 16
  , LowTypeSignedInt 32
  , LowTypeSignedInt 64
  ]

unsignedIntLowTypeList :: [LowType]
unsignedIntLowTypeList =
  [ LowTypeUnsignedInt 1
  , LowTypeUnsignedInt 2
  , LowTypeUnsignedInt 4
  , LowTypeUnsignedInt 8
  , LowTypeUnsignedInt 16
  , LowTypeUnsignedInt 32
  , LowTypeUnsignedInt 64
  ]

floatLowTypeList :: [LowType]
floatLowTypeList = [LowTypeFloat 16, LowTypeFloat 32, LowTypeFloat 64]

intAddConstantList :: [String]
intAddConstantList = flip map intLowTypeList $ \t -> "core." ++ show t ++ ".add"

intSubConstantList :: [String]
intSubConstantList = flip map intLowTypeList $ \t -> "core." ++ show t ++ ".sub"

intMulConstantList :: [String]
intMulConstantList = flip map intLowTypeList $ \t -> "core." ++ show t ++ ".mul"

intDivConstantList :: [String]
intDivConstantList = flip map intLowTypeList $ \t -> "core." ++ show t ++ ".div"
