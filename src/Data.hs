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

import           Data.IORef
import           Data.List
import           Data.Maybe                 (fromMaybe)

import qualified Data.PQueue.Min            as Q

import qualified Text.Show.Pretty           as Pr

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

data Pos
  = PosVar Identifier
  | PosConst Identifier
  | PosPi [(Identifier, Pos)]
          Pos
  | PosSigma [(Identifier, Pos)]
             Pos
  | PosSigmaIntro [Pos]
  | PosIndex Identifier
  | PosIndexIntro Index
  | PosDown Pos
  | PosDownIntroPiIntro Identifier -- the name of this lambda abstraction
                        [Identifier] -- arguments
                        Neg -- body
  | PosUp Pos
  | PosUniv
  deriving (Show)

data Neg
  = NegPiElimDownElim Identifier
                      [Identifier]
  | NegSigmaElim Identifier
                 [Identifier]
                 Neg
  | NegIndexElim Identifier
                 [(Index, Neg)]
  | NegUpIntro Pos
  | NegUpElim Identifier
              Neg
              Neg
  deriving (Show)

data Term
  = Value Pos
  | Comp Neg
  deriving (Show)

data Data
  = DataLocal Identifier
  | DataLabel Identifier
  | DataInt32 Int
  | DataStruct [Data]
  deriving (Show)

data Code
  = CodeReturn Data
  | CodeLet Identifier -- bind (we also use this to represent application)
            Data
            Code
  | CodeCall Identifier -- the register that stores the result of a function call
             Identifier -- the name of the function
             [Identifier] -- arguments
             Code -- continuation
  | CodeSwitch Identifier
               [(Index, Code)]
  | CodeExtractValue Identifier
                     Identifier
                     Int
                     Code
  | CodeFree Identifier
             Code
  deriving (Show)

data AsmMeta = AsmMeta
  { asmMetaLive :: [Identifier]
  , asmMetaDef  :: [Identifier]
  , asmMetaUse  :: [Identifier]
  } deriving (Show)

data AsmArg
  = AsmArgReg Identifier
  | AsmArgLabel Identifier
  | AsmArgImmediate Int
  deriving (Show)

-- AsmLoadWithOffset offset base dest == movq offset(base), dest
-- AsmStoreWithOffset val offset base == movq val, offset(base).
data AsmF a
  = AsmReturn Identifier
  | AsmLet Identifier
           AsmArg
           a
  | AsmExtractValue Identifier -- destination
                    Identifier -- base pointer
                    Int -- offset
                    a
  | AsmInsertValue AsmArg -- source
                   Identifier -- base pointer
                   Int -- offset
                   a
  | AsmCall Identifier
            AsmArg
            [Identifier]
            a
  | AsmCompare Identifier
               Identifier
               a
  | AsmJumpIfZero Identifier
                  a
  | AsmJump Identifier
  | AsmPush Identifier
            a
  | AsmPop Identifier
           a
  | AsmAddInt64 AsmArg -- addq {AsmArg}, {Identifier}
                Identifier
                a
  | AsmSubInt64 AsmArg -- subq {AsmArg}, {Identifier}
                Identifier
                a
  deriving (Show)

$(deriveShow1 ''AsmF)

type Asm = Cofree AsmF AsmMeta

instance (Show a) => Show (IORef a) where
  show a = show (unsafePerformIO (readIORef a))

initialIndexEnv :: [(Identifier, [Identifier])]
initialIndexEnv = [("int", [])]

-- isExternalConst :: Identifier -> WithEnv Bool
-- isExternalConst name = do
--   env <- get
--   return $ name `elem` map fst (constEnv env)
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
constraintToInt ConstraintPattern {}      = 0
constraintToInt ConstraintDelta {}        = 1
constraintToInt ConstraintBeta {}         = 2
constraintToInt ConstraintQuasiPattern {} = 3
constraintToInt ConstraintFlexRigid {}    = 4
constraintToInt ConstraintFlexFlex {}     = 5

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
  , metaMapSnapshot         :: [(Identifier, PreConstraint)]
  , substitutionSnapshot    :: Subst
  , caseJustification       :: Justification
  , savedJustification      :: Justification
  , alternatives            :: [[PreConstraint]]
  } deriving (Show)

data Env = Env
  { count             :: Int -- to generate fresh symbols
  , notationEnv       :: [(Tree, Tree)] -- macro transformers
  , reservedEnv       :: [Identifier] -- list of reserved keywords
  , indexEnv          :: [(Identifier, [Identifier])]
  , nameEnv           :: [(Identifier, Identifier)] -- used in alpha conversion
  , typeEnv           :: [(Identifier, Neut)] -- type environment
  , weakTermEnv       :: [(Identifier, Neut)]
  , termEnv           :: [(Identifier, Term)]
  , constEnv          :: [(Identifier, Neut)] -- (name, type)
  , constraintEnv     :: [PreConstraint]
  , constraintQueue   :: Q.MinQueue Constraint
  , metaMap           :: [(Identifier, PreConstraint)]
  , substitution      :: Subst
  , caseStack         :: [Case]
  , univConstraintEnv :: [(UnivLevel, UnivLevel)]
  , numConstraintEnv  :: [Identifier]
  , codeEnv           :: [(Identifier, ([Identifier], IORef Code))]
  , asmEnv            :: [(Identifier, Asm)]
  , regEnv            :: [(Identifier, Int)] -- variable to register
  , regVarList        :: [Identifier]
  , spill             :: Maybe Identifier
  , sizeEnv           :: [(Identifier, Int)] -- offset from stackpointer
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
    , termEnv = []
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
    , regEnv = []
    , regVarList = []
    , spill = Nothing
    , sizeEnv = []
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

constNameWith :: Identifier -> WithEnv ()
constNameWith s = modify (\e -> e {nameEnv = (s, s) : nameEnv e})

lookupTypeEnv :: String -> WithEnv (Maybe Neut)
lookupTypeEnv s = gets (lookup s . typeEnv)

lookupTypeEnv' :: String -> WithEnv Neut
lookupTypeEnv' s = do
  mt <- gets (lookup s . typeEnv)
  case mt of
    Nothing -> lift $ throwE $ s ++ " is not found in the type environment."
    Just t  -> return t

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

lookupTermEnv :: String -> WithEnv (Maybe Term)
lookupTermEnv s = gets (lookup s . termEnv)

lookupTermEnv' :: String -> WithEnv Term
lookupTermEnv' s = do
  mt <- gets (lookup s . termEnv)
  env <- get
  case mt of
    Nothing ->
      lift $
      throwE $
      s ++
      " is not found in the term environment. termenv: " ++
      Pr.ppShow (termEnv env)
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
    Nothing           -> lift $ throwE $ "no such code: " ++ show funName

insTypeEnv :: Identifier -> Neut -> WithEnv ()
insTypeEnv i t = modify (\e -> e {typeEnv = (i, t) : typeEnv e})

insConstEnv :: Identifier -> Neut -> WithEnv ()
insConstEnv i t = modify (\e -> e {constEnv = (i, t) : constEnv e})

insNumConstraintEnv :: Identifier -> WithEnv ()
insNumConstraintEnv x =
  modify (\e -> e {numConstraintEnv = x : numConstraintEnv e})

insTermEnv :: Identifier -> Term -> WithEnv ()
insTermEnv i t = modify (\e -> e {termEnv = (i, t) : termEnv e})

insWeakTermEnv :: Identifier -> Neut -> WithEnv ()
insWeakTermEnv i t = modify (\e -> e {weakTermEnv = (i, t) : weakTermEnv e})

lookupWeakTermEnv :: Identifier -> WithEnv Neut
lookupWeakTermEnv funName = do
  env <- get
  case lookup funName (weakTermEnv env) of
    Just body -> return body
    Nothing   -> lift $ throwE $ "no such weakterm: " ++ show funName

insCodeEnv :: Identifier -> [Identifier] -> Code -> WithEnv ()
insCodeEnv funName args body = do
  codeRef <- liftIO $ newIORef body
  modify (\e -> e {codeEnv = (funName, (args, codeRef)) : codeEnv e})

insAsmEnv :: Identifier -> Asm -> WithEnv ()
insAsmEnv funName asm = modify (\e -> e {asmEnv = (funName, asm) : asmEnv e})

insIndexEnv :: Identifier -> [Identifier] -> WithEnv ()
insIndexEnv name indexList =
  modify (\e -> e {indexEnv = (name, indexList) : indexEnv e})

lookupKind :: Index -> WithEnv (Maybe Identifier)
lookupKind IndexDefault = return Nothing
lookupKind (IndexInteger _) = return Nothing
lookupKind (IndexLabel name) = do
  env <- get
  lookupKind' name $ indexEnv env
  -- tmp <- lookupKind' name $ indexEnv env
  -- return $ Just tmp

lookupKind' ::
     Identifier -> [(Identifier, [Identifier])] -> WithEnv (Maybe Identifier)
lookupKind' _ [] = return Nothing
-- lookupKind' i [] = lift $ throwE $ "no such index defined: " ++ show i
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
    Just i  -> return i
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

insSizeEnv :: Identifier -> Int -> WithEnv ()
insSizeEnv name size = modify (\e -> e {sizeEnv = (name, size) : sizeEnv e})

lookupSizeEnv :: Identifier -> WithEnv (Maybe Int)
lookupSizeEnv s = gets (lookup s . sizeEnv)

lookupSizeEnv' :: Identifier -> WithEnv Int
lookupSizeEnv' s = do
  tmp <- gets (lookup s . sizeEnv)
  case tmp of
    Just i  -> return i
    Nothing -> lift $ throwE $ "the size of " ++ show s ++ " is not defined"

insConstraintEnv :: Context -> Neut -> Neut -> Neut -> WithEnv ()
insConstraintEnv ctx t1 t2 t =
  modify (\e -> e {constraintEnv = (ctx, t1, t2, t) : constraintEnv e})

insUnivConstraintEnv :: UnivLevel -> UnivLevel -> WithEnv ()
insUnivConstraintEnv t1 t2 =
  modify (\e -> e {univConstraintEnv = (t1, t2) : univConstraintEnv e})

lookupRegEnv :: Identifier -> WithEnv (Maybe Int)
lookupRegEnv s = gets (lookup s . regEnv)

lookupRegEnv' :: Identifier -> WithEnv Int
lookupRegEnv' s = do
  tmp <- gets (lookup s . regEnv)
  case tmp of
    Just i  -> return i
    Nothing -> lift $ throwE $ "no such register: " ++ show s

insRegEnv :: Identifier -> Int -> WithEnv ()
insRegEnv x i = modify (\e -> e {regEnv = (x, i) : regEnv e})

insSpill :: Identifier -> WithEnv ()
insSpill x = modify (\e -> e {spill = Just x})

lookupSpill :: WithEnv (Maybe Identifier)
lookupSpill = gets spill

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
sizeOfLowType (LowTypeInt _)     = 8
sizeOfLowType (LowTypePointer _) = 8
sizeOfLowType (LowTypeStruct ts) = sum $ map sizeOfLowType ts

toLowType :: Neut -> WithEnv LowType
toLowType (_ :< NeutVar _) = return $ LowTypeInt 32 -- (*1)
toLowType (_ :< NeutPi _ _) = return $ LowTypePointer $ LowTypeInt 8
toLowType (_ :< NeutSigma xts t) = do
  ts' <- mapM toLowType (map snd xts ++ [t])
  let ts'' = map LowTypePointer ts'
  return $ LowTypeStruct ts''
toLowType (_ :< NeutIndex _) = return $ LowTypeInt 32
toLowType (_ :< NeutUniv _) = return $ LowTypeInt 32
toLowType v = lift $ throwE $ "Asm.toLowType: " ++ show v ++ " is not a type"

sizeOf :: Identifier -> WithEnv Int
sizeOf x = do
  t <- lookupTypeEnv' x
  sizeOfType t

getArgRegList :: WithEnv [Identifier]
getArgRegList = do
  rdi <- getRDI
  rsi <- getRSI
  rdx <- getRDX
  rcx <- getRCX
  r8 <- getR8
  r9 <- getR9
  return [rdi, rsi, rdx, rcx, r8, r9]

regList :: [Identifier]
regList =
  [ "r15"
  , "r14"
  , "r13"
  , "r12"
  , "r11"
  , "r10"
  , "rbp"
  , "rbx"
  , "r9"
  , "r8"
  , "rcx"
  , "rdx"
  , "rsi"
  , "rdi"
  , "rax"
  , "rsp" -- rsp is not used in register allocation
  ]

initRegVar :: WithEnv ()
initRegVar = do
  xs <- mapM newNameWith regList
  forM_ (zip regList xs) $ \(regVar, newVar) ->
    modify (\e -> e {nameEnv = (regVar, newVar) : nameEnv e})
  modify (\e -> e {regVarList = xs ++ regVarList e})
  forM_ (zip [0 ..] xs) $ \(i, regVar) -> insRegEnv regVar i -- precolored

isRegVar :: Identifier -> WithEnv Bool
isRegVar x = do
  env <- get
  return $ x `elem` regVarList env

getRegVarIndex :: Identifier -> WithEnv Int
getRegVarIndex x = do
  x' <- lookupNameEnv' x
  env <- get
  case elemIndex x' (regVarList env) of
    Just i  -> return i
    Nothing -> lift $ throwE $ x' ++ " is not a register variable"

toRegName :: Identifier -> WithEnv Identifier
toRegName x = do
  i <- lookupRegEnv' x
  return $ regList !! i

toRegNumList :: [Identifier] -> WithEnv [Int]
toRegNumList [] = return []
toRegNumList (x:xs) = do
  is <- toRegNumList xs
  mi <- lookupRegEnv x
  case mi of
    Just i  -> return $ i : is
    Nothing -> return is

getR15 :: WithEnv Identifier
getR15 = lookupNameEnv' "r15"

getR14 :: WithEnv Identifier
getR14 = lookupNameEnv' "r14"

getR13 :: WithEnv Identifier
getR13 = lookupNameEnv' "r13"

getR12 :: WithEnv Identifier
getR12 = lookupNameEnv' "r12"

getR11 :: WithEnv Identifier
getR11 = lookupNameEnv' "r11"

getR10 :: WithEnv Identifier
getR10 = lookupNameEnv' "r10"

getRBX :: WithEnv Identifier
getRBX = lookupNameEnv' "rbx"

getR9 :: WithEnv Identifier
getR9 = lookupNameEnv' "r9"

getR8 :: WithEnv Identifier
getR8 = lookupNameEnv' "r8"

getRCX :: WithEnv Identifier
getRCX = lookupNameEnv' "rcx"

getRDX :: WithEnv Identifier
getRDX = lookupNameEnv' "rdx"

getRSI :: WithEnv Identifier
getRSI = lookupNameEnv' "rsi"

getRDI :: WithEnv Identifier
getRDI = lookupNameEnv' "rdi"

getRAX :: WithEnv Identifier
getRAX = lookupNameEnv' "rax"

getRBP :: WithEnv Identifier
getRBP = lookupNameEnv' "rbp"

getRSP :: WithEnv Identifier
getRSP = lookupNameEnv' "rsp"

varsInAsmArg :: AsmArg -> [Identifier]
varsInAsmArg (AsmArgReg x)       = [x]
varsInAsmArg (AsmArgLabel _)     = []
varsInAsmArg (AsmArgImmediate _) = []
