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
  deriving (Show)

data NeutF a
  = NeutVar Identifier
  | NeutPi (Identifier, a)
           a
  | NeutPiIntro (Identifier, a)
                a
  | NeutPiElim a
               a
  | NeutSigma (Identifier, a)
              a
  | NeutSigmaIntro a
                   a
  | NeutSigmaElim a
                  (Identifier, Identifier)
                  a
  | NeutTop
  | NeutTopIntro
  | NeutUniv UnivLevel
  | NeutMu Identifier
           a
  | NeutHole Identifier
  | NeutSubst a -- explicit substitution for types
              [(Identifier, a)]

type Neut = Cofree NeutF Identifier

$(deriveShow1 ''NeutF)

data Pos
  = PosVar Identifier
  | PosPi [(Identifier, Pos)]
          Pos
  | PosSigma [(Identifier, Pos)]
             Pos
  | PosSigmaIntro [Identifier]
  | PosTop
  | PosTopIntro
  | PosDown Pos
  | PosDownIntroPiIntro [Identifier]
                        Neg
  | PosUp Pos
  | PosUniv
  deriving (Show)

data Neg
  = NegPiElimDownElim Identifier
                      [Identifier]
  | NegSigmaElim Identifier
                 (Identifier, Identifier) -- exists-elim
                 Neg
  | NegUpIntro Pos
  | NegUpElim Identifier
              Neg
              Neg
  deriving (Show)

data Term
  = Value Pos
  | Comp Neg
  deriving (Show)

type Index = [Int]

data Data
  = DataLocal Identifier
  | DataLabel Identifier
  | DataInt32 Int
  | DataStruct [Identifier]
  deriving (Show)

type Address = Identifier

data Code
  = CodeReturn Data
  | CodeLet Identifier -- bind (we also use this to represent application)
            Data
            Code
  | CodeCall Identifier -- the register that stores the result of a function call
             Identifier -- the name of the function
             [Identifier] -- arguments
             Code -- continuation
  | CodeExtractValue Identifier
                     Identifier
                     Int
                     Code
  deriving (Show)

data AsmMeta = AsmMeta
  { asmMetaLive :: [Identifier]
  , asmMetaDef  :: [Identifier]
  , asmMetaUse  :: [Identifier]
  } deriving (Show)

data AsmArg
  = AsmArgReg Identifier
  | AsmArgImmediate Int
  deriving (Show)

-- AsmLoadWithOffset offset base dest == movq offset(base), dest
-- AsmStoreWithOffset val offset base == movq val, offset(base).
data AsmF a
  = AsmReturn Identifier
  | AsmMov Identifier
           AsmArg
           a
  | AsmLoadWithOffset Int -- movq {Int}({Identifier}), {Identifier}; cont
                      Identifier
                      Identifier
                      a
  | AsmStoreWithOffset AsmArg -- movq {AsmArg}, {Int}({Identifier}); cont
                       Int
                       Identifier
                       a
  | AsmCall Identifier
            Identifier
            [Identifier]
            a
  | AsmPush Identifier
            a
  | AsmPop Identifier
           a
  | AsmAddInt64 AsmArg -- subq {AsmArg}, {Identifier}
                Identifier
                a
  | AsmSubInt64 AsmArg -- subq {AsmArg}, {Identifier}
                Identifier
                a

$(deriveShow1 ''AsmF)

type Asm = Cofree AsmF AsmMeta

instance (Show a) => Show (IORef a) where
  show a = show (unsafePerformIO (readIORef a))

data Env = Env
  { count             :: Int -- to generate fresh symbols
  , notationEnv       :: [(Tree, Tree)] -- macro transformers
  , reservedEnv       :: [Identifier] -- list of reserved keywords
  , nameEnv           :: [(Identifier, Identifier)] -- used in alpha conversion
  , typeEnv           :: [(Identifier, Neut)] -- type environment
  , termEnv           :: [(Identifier, Term)]
  , constraintEnv     :: [(Neut, Neut)] -- used in type inference
  , univConstraintEnv :: [(UnivLevel, UnivLevel)]
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
    , nameEnv = []
    , typeEnv = []
    , termEnv = []
    , constraintEnv = []
    , univConstraintEnv = []
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

insTermEnv :: Identifier -> Term -> WithEnv ()
insTermEnv i t = modify (\e -> e {termEnv = (i, t) : termEnv e})

insCodeEnv :: Identifier -> [Identifier] -> Code -> WithEnv ()
insCodeEnv funName args body = do
  codeRef <- liftIO $ newIORef body
  modify (\e -> e {codeEnv = (funName, (args, codeRef)) : codeEnv e})

insAsmEnv :: Identifier -> Asm -> WithEnv ()
insAsmEnv funName asm = modify (\e -> e {asmEnv = (funName, asm) : asmEnv e})

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

insConstraintEnv :: Neut -> Neut -> WithEnv ()
insConstraintEnv t1 t2 =
  modify (\e -> e {constraintEnv = (t1, t2) : constraintEnv e})

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
    _ :< NeutPi _ tcod -> do
      meta <- newNameWith "meta"
      insTypeEnv meta tcod
      appFold (meta :< NeutPiElim e term) ts
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
  tArg@(argMeta :< _) <- lookupTypeEnv' arg
  tmp <- bindFormalArgs xs c
  meta <- newNameWith "meta"
  univMeta <- newNameWith "meta"
  univ <- lookupTypeEnv' argMeta
  insTypeEnv univMeta univ
  insTypeEnv meta (univMeta :< NeutPi (arg, tArg) tLam)
  return $ meta :< NeutPiIntro (arg, tArg) tmp

forallArgs :: Neut -> (Neut, [(Identifier, Neut, Identifier)])
forallArgs (meta :< NeutPi (i, vt) t) = do
  let (body, xs) = forallArgs t
  (body, (i, vt, meta) : xs)
forallArgs body = (body, [])

coForallArgs :: (Neut, [(Identifier, Neut, Identifier)]) -> Neut
coForallArgs (t, []) = t
coForallArgs (t, (i, tdom, meta):ts) =
  coForallArgs (meta :< NeutPi (i, tdom) t, ts)

funAndArgs :: Neut -> WithEnv (Neut, [(Identifier, Neut)])
funAndArgs (i :< NeutPiElim e v) = do
  (fun, xs) <- funAndArgs e
  return (fun, (i, v) : xs)
funAndArgs c = return (c, [])

coFunAndArgs :: (Neut, [(Identifier, Neut)]) -> Neut
coFunAndArgs (term, [])        = term
coFunAndArgs (term, (i, v):xs) = coFunAndArgs (i :< NeutPiElim term v, xs)

var :: Neut -> [Identifier]
var (_ :< NeutVar s) = [s]
var (_ :< NeutPi (i, tdom) tcod) = var tdom ++ filter (/= i) (var tcod)
var (_ :< NeutPiIntro (s, _) e) = filter (/= s) (var e)
var (_ :< NeutPiElim e v) = var e ++ var v
var (_ :< NeutSigma (i, tdom) tcod) = var tdom ++ filter (/= i) (var tcod)
var (_ :< NeutSigmaIntro v1 v2) = var v1 ++ var v2
var (_ :< NeutSigmaElim e1 (x, y) e2) =
  var e1 ++ filter (\s -> s /= x && s /= y) (var e2)
var (_ :< NeutTop) = []
var (_ :< NeutTopIntro) = []
var (_ :< NeutUniv _) = []
var (_ :< NeutMu s e) = filter (/= s) (var e)
var (_ :< NeutHole _) = []
var e@(_ :< NeutSubst _ _) = var $ reduce e

type Subst = [(Identifier, Neut)]

-- proceed explicit substitution
subst :: Subst -> Neut -> Neut
subst sub e = reduce ("" :< NeutSubst e sub)

type SubstIdent = [(Identifier, Identifier)]

substIdent :: SubstIdent -> Identifier -> Identifier
substIdent sub x = fromMaybe x (lookup x sub)

compose :: Subst -> Subst -> Subst
compose s1 s2 = do
  let domS2 = map fst s2
  let codS2 = map snd s2
  let codS2' = map (subst s1) codS2
  let fromS1 = filter (\(ident, _) -> ident `notElem` domS2) s1
  fromS1 ++ zip domS2 codS2'

reduce :: Neut -> Neut
reduce (i :< NeutPiElim e1 e2) = do
  let e2' = reduce e2
  let e1' = reduce e1
  case e1' of
    _ :< NeutPiIntro (arg, _) body -> do
      let sub = [(arg, reduce e2)]
      let _ :< body' = subst sub body
      reduce $ i :< body'
    _ -> i :< NeutPiElim e1' e2'
reduce (i :< NeutSigmaIntro e1 e2) = do
  let e1' = reduce e1
  let e2' = reduce e2
  i :< NeutSigmaIntro e1' e2'
reduce (i :< NeutSigmaElim e (x, y) body) = do
  let e' = reduce e
  case e of
    _ :< NeutSigmaIntro e1 e2 -> do
      let sub = [(x, reduce e1), (y, reduce e2)]
      let _ :< body' = subst sub body
      reduce $ i :< body'
    _ -> i :< NeutSigmaElim e' (x, y) body
reduce (meta :< NeutMu s c) = do
  let c' = reduce c
  meta :< NeutMu s c'
reduce (_ :< NeutSubst (k :< NeutVar s) sub) =
  fromMaybe (k :< NeutVar s) (lookup s sub)
reduce (j :< NeutSubst (i :< NeutPi (s, tdom) tcod) sub) = do
  let tdom' = reduce (j :< NeutSubst tdom sub)
  let tcod' = reduce (j :< NeutSubst tcod sub)
  i :< NeutPi (s, tdom') tcod'
reduce (j :< NeutSubst (i :< NeutPiIntro (s, tdom) body) sub) = do
  let tdom' = reduce (j :< NeutSubst tdom sub)
  let body' = reduce (j :< NeutSubst body sub)
  i :< NeutPiIntro (s, tdom') body'
reduce (j :< NeutSubst (i :< NeutPiElim e1 e2) sub) = do
  let e1' = reduce (j :< NeutSubst e1 sub)
  let e2' = reduce (j :< NeutSubst e2 sub)
  i :< NeutPiElim e1' e2'
reduce (j :< NeutSubst (i :< NeutSigma (s, tdom) tcod) sub) = do
  let tdom' = reduce (j :< NeutSubst tdom sub)
  let tcod' = reduce (j :< NeutSubst tcod sub)
  i :< NeutSigma (s, tdom') tcod'
reduce (j :< NeutSubst (i :< NeutSigmaIntro e1 e2) sub) = do
  let e1' = reduce (j :< NeutSubst e1 sub)
  let e2' = reduce (j :< NeutSubst e2 sub)
  i :< NeutSigmaIntro e1' e2'
reduce (j :< NeutSubst (i :< NeutSigmaElim e1 (x, y) e2) sub) = do
  let e1' = reduce (j :< NeutSubst e1 sub)
  let e2' = reduce (j :< NeutSubst e2 sub)
  i :< NeutSigmaElim e1' (x, y) e2'
reduce (_ :< NeutSubst (i :< NeutTop) _) = i :< NeutTop
reduce (_ :< NeutSubst (i :< NeutTopIntro) _) = i :< NeutTopIntro
reduce (_ :< NeutSubst (i :< NeutUniv l) _) = i :< NeutUniv l
reduce (j :< NeutSubst (i :< NeutMu x e) sub) = do
  let e' = reduce (j :< NeutSubst e sub)
  i :< NeutMu x e'
reduce self@(_ :< NeutSubst (_ :< NeutHole x) sub) =
  fromMaybe self (lookup x sub)
reduce (_ :< NeutSubst (i :< NeutSubst e sub1) sub2) =
  reduce $ i :< NeutSubst e (sub1 ++ sub2)
reduce e = e

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
sizeOfType (_ :< NeutSigma (_, t1) t2) = do
  i1 <- sizeOfType t1
  i2 <- sizeOfType t2
  return $ i1 + i2
sizeOfType (_ :< NeutTop) = return 4
sizeOfType (_ :< NeutUniv _) = return 4
sizeOfType v = lift $ throwE $ "Asm.sizeOfType: " ++ show v ++ " is not a type"

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

-- rsp is colored by -1, and not used in register allocation
initRegVar :: WithEnv ()
initRegVar = do
  xs <- mapM (const newName) regList
  forM_ (zip regList xs) $ \(regVar, newVar) ->
    modify (\e -> e {nameEnv = (regVar, newVar) : nameEnv e})
  modify (\e -> e {regVarList = xs})
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
varsInAsmArg (AsmArgImmediate _) = []

toPiIntroSeq :: Neut -> WithEnv (Neut, [Identifier])
toPiIntroSeq (_ :< NeutPiIntro (x, _) body) = do
  (body', args) <- toPiIntroSeq body
  return (body', x : args)
toPiIntroSeq t = return (t, [])

toSigmaIntroSeq :: Neut -> WithEnv [Neut]
toSigmaIntroSeq (_ :< NeutSigmaIntro e1 e2) = do
  rest <- toSigmaIntroSeq e2
  return $ e1 : rest
toSigmaIntroSeq t = return [t]

toPiSeq :: Neut -> WithEnv (Neut, [(Identifier, Neut)])
toPiSeq (_ :< NeutPi (x, t) body) = do
  (body', args) <- toPiSeq body
  return (body', (x, t) : args)
toPiSeq t = return (t, [])

toSigmaSeq :: Neut -> WithEnv (Neut, [(Identifier, Neut)])
toSigmaSeq (_ :< NeutSigma (x, t) body) = do
  (body', args) <- toSigmaSeq body
  return (body', (x, t) : args)
toSigmaSeq t = return (t, [])
