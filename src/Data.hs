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
  | NeutUniv
  | NeutMu Identifier
           a
  | NeutHole Identifier

type Neut = Cofree NeutF Identifier

$(deriveShow1 ''NeutF)

data PosF c v
  = PosVar Identifier
  | PosPi [(Identifier, v)]
          v
  | PosSigma [(Identifier, v)]
             v
  | PosSigmaIntro [Identifier]
  | PosTop
  | PosTopIntro
  | PosDown v
  | PosDownIntroPiIntro [Identifier]
                        c
  | PosUp v
  | PosUniv

data NegF v c
  = NegPiElimDownElim Identifier
                      [Identifier]
  | NegSigmaElim Identifier
                 (Identifier, Identifier) -- exists-elim
                 c
  | NegUpIntro v
  | NegUpElim Identifier
              c
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
  | AsmLoadWithOffset Int
                      Identifier
                      Identifier
                      a
  | AsmStoreWithOffset AsmArg
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

$(deriveShow1 ''AsmF)

type Asm = Cofree AsmF AsmMeta

instance (Show a) => Show (IORef a) where
  show a = show (unsafePerformIO (readIORef a))

data Env = Env
  { count         :: Int -- to generate fresh symbols
  , notationEnv   :: [(Tree, Tree)] -- macro transformers
  , reservedEnv   :: [Identifier] -- list of reserved keywords
  , nameEnv       :: [(Identifier, Identifier)] -- used in alpha conversion
  , typeEnv       :: [(Identifier, Neut)] -- type environment
  , polTypeEnv    :: [(Identifier, Pos)] -- polarized type environment
  , termEnv       :: [(Identifier, Term)]
  , constraintEnv :: [(Neut, Neut)] -- used in type inference
  , codeEnv       :: [(Identifier, ([Identifier], IORef Code))]
  , asmEnv        :: [(Identifier, Asm)]
  , regEnv        :: [(Identifier, Int)] -- variable to register
  , regVarList    :: [Identifier]
  , spill         :: Maybe Identifier
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
    , polTypeEnv = []
    , termEnv = []
    , constraintEnv = []
    , codeEnv = []
    , asmEnv = []
    , regEnv = []
    , regVarList = []
    , spill = Nothing
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

lookupPolTypeEnv :: String -> WithEnv (Maybe Pos)
lookupPolTypeEnv s = gets (lookup s . polTypeEnv)

lookupPolTypeEnv' :: String -> WithEnv Pos
lookupPolTypeEnv' s = do
  mt <- gets (lookup s . polTypeEnv)
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

insPolTypeEnv :: Identifier -> Pos -> WithEnv ()
insPolTypeEnv i t = modify (\e -> e {polTypeEnv = (i, t) : polTypeEnv e})

insCodeEnv :: Identifier -> [Identifier] -> Code -> WithEnv ()
insCodeEnv funName args body = do
  codeRef <- liftIO $ newIORef body
  modify (\e -> e {codeEnv = (funName, (args, codeRef)) : codeEnv e})

insAsmEnv :: Identifier -> Asm -> WithEnv ()
insAsmEnv funName asm = modify (\e -> e {asmEnv = (funName, asm) : asmEnv e})

insConstraintEnv :: Neut -> Neut -> WithEnv ()
insConstraintEnv t1 t2 =
  modify (\e -> e {constraintEnv = (t1, t2) : constraintEnv e})

lookupRegEnv :: Identifier -> WithEnv (Maybe Int)
lookupRegEnv s = gets (lookup s . regEnv)

lookupRegEnv' :: Identifier -> WithEnv Identifier
lookupRegEnv' s = do
  tmp <- gets (lookup s . regEnv)
  case tmp of
    Just i  -> return $ numToReg i
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
  tArg <- lookupTypeEnv' arg
  tmp <- bindFormalArgs xs c
  meta <- newNameWith "meta"
  univMeta <- newNameWith "meta"
  insTypeEnv univMeta (univMeta :< NeutUniv)
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
var (_ :< NeutPiIntro (s, tdom) e) = var tdom ++ filter (/= s) (var e)
var (_ :< NeutPiElim e v) = var e ++ var v
var (_ :< NeutSigma (i, tdom) tcod) = var tdom ++ filter (/= i) (var tcod)
var (_ :< NeutSigmaIntro v1 v2) = var v1 ++ var v2
var (_ :< NeutSigmaElim e1 (x, y) e2) =
  var e1 ++ filter (\s -> s /= x && s /= y) (var e2)
var (_ :< NeutTop) = []
var (_ :< NeutTopIntro) = []
var (_ :< NeutUniv) = []
var (_ :< NeutMu s e) = filter (/= s) (var e)
var (_ :< NeutHole _) = []

type Subst = [(Identifier, Neut)]

subst :: Subst -> Neut -> Neut
subst _ (j :< NeutVar s) = j :< NeutVar s
subst sub (j :< NeutPi (s, tdom) tcod) = do
  let tdom' = subst sub tdom
  let tcod' = subst sub tcod -- note that we don't have to drop s from sub, thanks to rename.
  j :< NeutPi (s, tdom') tcod'
subst sub (j :< NeutPiIntro (s, tdom) body) = do
  let tdom' = subst sub tdom
  let body' = subst sub body
  j :< NeutPiIntro (s, tdom') body'
subst sub (j :< NeutPiElim e1 e2) = do
  let e1' = subst sub e1
  let e2' = subst sub e2
  j :< NeutPiElim e1' e2'
subst sub (j :< NeutSigma (s, tdom) tcod) = do
  let tdom' = subst sub tdom
  let tcod' = subst sub tcod
  j :< NeutSigma (s, tdom') tcod'
subst sub (j :< NeutSigmaIntro e1 e2) = do
  let e1' = subst sub e1
  let e2' = subst sub e2
  j :< NeutSigmaIntro e1' e2'
subst sub (j :< NeutSigmaElim e1 (x, y) e2) = do
  let e1' = subst sub e1
  let e2' = subst sub e2
  j :< NeutSigmaElim e1' (x, y) e2'
subst _ (j :< NeutTop) = j :< NeutTop
subst _ (j :< NeutTopIntro) = j :< NeutTopIntro
subst _ (j :< NeutUniv) = j :< NeutUniv
subst sub (j :< NeutMu x e) = do
  let e' = subst sub e
  j :< NeutMu x e'
subst sub (j :< NeutHole s) = fromMaybe (j :< NeutHole s) (lookup s sub)

type SubstIdent = [(Identifier, Identifier)]

substIdent :: SubstIdent -> Identifier -> Identifier
substIdent sub x = fromMaybe x (lookup x sub)

substPos :: SubstIdent -> Pos -> Pos
substPos sub (Pos (j :< PosVar s)) = Pos $ j :< PosVar (substIdent sub s)
substPos sub (Pos (j :< PosPi xts tcod)) = do
  undefined
  -- let Pos tdom' = substPos sub $ Pos tdom
  -- let Pos tcod' = substPos sub $ Pos tcod
  -- Pos $ j :< PosPi (s, tdom') tcod'
substPos sub (Pos (j :< PosSigma xts tcod)) = do
  undefined
  -- let Pos tdom' = substPos sub $ Pos tdom
  -- let Pos tcod' = substPos sub $ Pos tcod
  -- Pos $ j :< PosSigma (s, tdom') tcod'
substPos sub (Pos (j :< PosSigmaIntro xs)) = do
  let xs' = map (substIdent sub) xs
  -- let x' = substIdent sub x
  -- let y' = substIdent sub y
  Pos $ j :< PosSigmaIntro xs'
substPos sub (Pos (j :< PosDown t)) = do
  let Pos t' = substPos sub $ Pos t
  Pos $ j :< PosDown t'
substPos sub (Pos (j :< PosDownIntroPiIntro s body)) = do
  let body' = substNeg sub body
  Pos $ j :< PosDownIntroPiIntro s body'
substPos sub (Pos (j :< PosUp t)) = do
  let Pos t' = substPos sub $ Pos t
  Pos $ j :< PosUp t'
substPos _ (Pos (j :< PosTop)) = Pos $ j :< PosTop
substPos _ (Pos (j :< PosTopIntro)) = Pos $ j :< PosTopIntro
substPos _ (Pos (j :< PosUniv)) = Pos $ j :< PosUniv

substNeg :: SubstIdent -> Neg -> Neg
substNeg sub (Neg (j :< NegPiElimDownElim e vs)) = do
  let e' = substIdent sub e
  let vs' = map (substIdent sub) vs
  Neg $ j :< NegPiElimDownElim e' vs'
substNeg sub (Neg (j :< NegSigmaElim v (x, y) e)) = do
  let v' = substIdent sub v
  let Neg e' = substNeg sub $ Neg e
  Neg $ j :< NegSigmaElim v' (x, y) e'
substNeg sub (Neg (j :< NegUpIntro v)) = do
  let v' = substPos sub v
  Neg $ j :< NegUpIntro v'
substNeg sub (Neg (j :< NegUpElim x e1 e2)) = do
  let Neg e1' = substNeg sub $ Neg e1
  let Neg e2' = substNeg sub $ Neg e2
  Neg $ j :< NegUpElim x e1' e2'

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
reduce t = t

-- bindWithLet x e1 e2 ~> let x := e1 in e2
bindWithLet :: Identifier -> Neut -> Neut -> WithEnv Neut
bindWithLet x e1 e2 = do
  i <- newName
  j <- newName
  tdom <- lookupTypeEnv' x
  return $ j :< NeutPiElim (i :< NeutPiIntro (x, tdom) e2) e1

pendSubst :: Subst -> Neut -> WithEnv Neut
pendSubst [] e = return e
pendSubst ((x, e1):rest) e = do
  e' <- pendSubst rest e
  bindWithLet x e1 e'

-- wrap :: NeutF Neut -> WithEnv Neut
wrap :: f (Cofree f Identifier) -> WithEnv (Cofree f Identifier)
wrap a = do
  meta <- newNameWith "meta"
  return $ meta :< a

wrapType :: NeutF Neut -> WithEnv Neut
wrapType t = do
  meta <- newNameWith "meta"
  u <- wrap NeutUniv
  insTypeEnv meta u
  return $ meta :< t

numToReg :: Int -> Identifier
numToReg = undefined

addMeta :: AsmF Asm -> WithEnv Asm
addMeta pc = do
  meta <- emptyAsmMeta
  return $ meta :< pc

emptyAsmMeta :: WithEnv AsmMeta
emptyAsmMeta =
  return $ AsmMeta {asmMetaLive = [], asmMetaDef = [], asmMetaUse = []}

data Register
  = General Identifier
  | Specified Identifier
  deriving (Show)

regList :: [Identifier]
regList =
  [ "r15"
  , "r14"
  , "r13"
  , "r12"
  , "r11"
  , "r10"
  , "rbx"
  , "r9"
  , "r8"
  , "rcx"
  , "rdx"
  , "rsi"
  , "rdi"
  , "rax"
  ]

regNthArg :: Int -> Identifier
regNthArg i =
  if 0 <= i && i < 6
    then regList !! (length regList - (1 + i))
    else error "regNthArg"

getNthArgRegVar :: Int -> WithEnv Identifier
getNthArgRegVar i = do
  env <- get
  if 0 <= i && i < 6
    then return $ regVarList env !! (length (regVarList env) - (2 + i))
    else error "regNthArg"

getArgRegList :: WithEnv [Identifier]
getArgRegList = do
  tmp <- gets (take 6 . drop 7 . regVarList)
  return $ reverse tmp

regRetReg :: Identifier
regRetReg = regList !! (length regList - 1)

regArgReg :: [Identifier]
regArgReg = ["rdi", "rsi", "rdx", "rcx", "r8", "r9", "r10", "r11"]

initRegVar :: WithEnv ()
initRegVar = do
  xs <- mapM (const newName) regList
  modify (\e -> e {regVarList = xs})
  forM_ (zip [0 ..] xs) $ \(i, regVar) -> insRegEnv regVar i -- precolored

isRegVar :: Identifier -> WithEnv Bool
isRegVar x = do
  env <- get
  return $ x `elem` regVarList env

getRegVarIndex :: Identifier -> WithEnv Int
getRegVarIndex x = do
  env <- get
  case elemIndex x (regVarList env) of
    Just i  -> return i
    Nothing -> lift $ throwE $ x ++ " is not a register variable"

getIthReg :: Int -> WithEnv Identifier
getIthReg i = do
  env <- get
  return $ regVarList env !! i

getR15 :: WithEnv Identifier
getR15 = getIthReg 0

getR14 :: WithEnv Identifier
getR14 = getIthReg 1

getR13 :: WithEnv Identifier
getR13 = getIthReg 2

getR12 :: WithEnv Identifier
getR12 = getIthReg 3

getR11 :: WithEnv Identifier
getR11 = getIthReg 4

getR10 :: WithEnv Identifier
getR10 = getIthReg 5

getRBX :: WithEnv Identifier
getRBX = getIthReg 6

getR9 :: WithEnv Identifier
getR9 = getIthReg 7

getR8 :: WithEnv Identifier
getR8 = getIthReg 8

getRCX :: WithEnv Identifier
getRCX = getIthReg 9

getRDX :: WithEnv Identifier
getRDX = getIthReg 10

getRSI :: WithEnv Identifier
getRSI = getIthReg 11

getRDI :: WithEnv Identifier
getRDI = getIthReg 12

getRAX :: WithEnv Identifier
getRAX = getIthReg 13

-- stack pointer
regSp :: Identifier
regSp = "rsp"

-- base pointer
regBp :: Identifier
regBp = "rbp"
