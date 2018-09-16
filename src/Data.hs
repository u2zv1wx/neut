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

data WeakType
  = WeakTypeVar Identifier
  | WeakTypeArrow WeakType -- (arrow A A)  (i.e. forall (_ : A) { A })
                  WeakType
  | WeakTypeForall Identifier -- (forall x A)
                   WeakType
  | WeakTypePi [(Identifier, WeakType)] -- (pi ((x1 A1) ... (xn An)))
  | WeakTypeProduct WeakType -- (product A A)
                    WeakType
  | WeakTypeExists Identifier -- (exists x A)
                   WeakType
  | WeakTypeSigma [(Identifier, WeakType)] -- (sigma ((x1 A1) ... (xn An)))
  | WeakTypeTop -- top
  | WeakTypeHole Identifier
  | WeakTypeApp WeakType
                WeakType
  | WeakTypeEnum Identifier
  | WeakTypeSubst WeakType -- t1 { x := t2 }. explicit substitution for type inference.
                  Identifier
                  WeakType
  deriving (Show)

data Type
  = TypeVar Identifier
  | TypeArrow Type
              Type
  | TypeForall Identifier
               Type
  | TypePi Identifier
           [(Identifier, Type)]
  | TypeProduct Type
                Type
  | TypeExists Identifier
               Type
  | TypeSigma Identifier
              [(Identifier, Type)]
  | TypeTop
  | TypeUp
  | TypeDown
  deriving (Show)

data NeutF a
  = NeutVar Identifier -- x
  | NeutArrowIntro (Identifier, WeakType) -- (lambda x e)
                   a
  | NeutArrowElim a -- (e e)
                  a
  | NeutForallIntro Identifier -- (forall x e)
                    a
  | NeutForallElim a -- (instance e A)
                   WeakType
  | NeutPiIntro [(Identifier, a)] -- (struct ((x1 e1) ... (xn en)))
  | NeutPiElim a -- (project e e)
               a
  | NeutProductIntro a -- (pair e e)
                     a
  | NeutProductElim a -- (case e ((pair x y) e))
                    (Identifier, Identifier)
                    a
  | NeutExistsIntro Identifier -- (exists x e)
                    a
  | NeutExistsElim a -- (case e ((exists x y) e))
                   (Identifier, Identifier)
                   a
  | NeutSigmaIntro a -- (inject x e)
                   a
  | NeutSigmaElim a -- (case e (((inject x1 e1) body1) ... ((inject xn en) bodyn)))
                  [((Identifier, Identifier), a)]
  | NeutTopIntro -- unit
  | NeutMu Identifier -- (mu x e)
           a

type Neut = Cofree NeutF Identifier

$(deriveShow1 ''NeutF)

data PosF c v
  = PosVar Identifier
  | PosProductIntro Identifier
                    Identifier
  | PosExistsIntro Identifier
                   Identifier
  | PosSigmaIntro Identifier
                  Identifier
  | PosTopIntro
  | PosDownIntroArrowIntro [Identifier]
                           c
  | PosDownIntroForallIntro [Identifier]
                            c
  | PosDownIntroPiIntro [(Identifier, c)]

data NegF v c
  = NegArrowElimDownElim Identifier
                         [Identifier]
  | NegForallElimDownElim Identifier
                          [Identifier]
  | NegPiElimDownElim Identifier
                      Identifier
  | NegProductElim Identifier
                   (Identifier, Identifier)
                   c
  | NegExistsElim Identifier
                  (Identifier, Identifier)
                  c
  | NegSigmaElim Identifier
                 [((Identifier, Identifier), c)]
  | NegUpIntro v -- up-intro
  | NegUpElim Identifier -- up-elim
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
  | DataGlobal Identifier
  | DataNullPtr
  | DataStruct [Data]
  deriving (Show)

data Code
  = CodeReturn Data
  | CodeLet Identifier -- bind (we also use this to represent application)
            Data
            Code
  | CodeCall Identifier -- the register that stores the result of a function call
             Data -- the name of the function (DataLocal or DataGlobal)
             [Data] -- arguments
             Code -- continuation
  | CodeExtractValue Identifier
                     Data
                     Int
                     Code
  deriving (Show)

data Env = Env
  { count         :: Int -- to generate fresh symbols
  , notationEnv   :: [(Tree, Tree)] -- macro transformers
  , reservedEnv   :: [Identifier] -- list of reserved keywords
  , enumEnv       :: [(Identifier, [Identifier])] -- (label-set-name, [list of labels])
  , nameEnv       :: [(Identifier, Identifier)] -- used in alpha conversion
  , typeEnv       :: [(Identifier, WeakType)] -- type environment
  , polTypeEnv    :: [(Identifier, Pos)] -- polarized type environment
  , termEnv       :: [(Identifier, Term)]
  , constraintEnv :: [(WeakType, WeakType)] -- used in type inference
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
    , enumEnv = []
    , nameEnv = []
    , typeEnv = []
    , polTypeEnv = []
    , termEnv = []
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

lookupTypeEnv :: String -> WithEnv (Maybe WeakType)
lookupTypeEnv s = gets (lookup s . typeEnv)

lookupTypeEnv' :: String -> WithEnv WeakType
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

lookupCodeEnv :: Identifier -> WithEnv ([Identifier], Code)
lookupCodeEnv funName = do
  env <- get
  case lookup funName (codeEnv env) of
    Just (args, body) -> return (args, body)
    Nothing           -> lift $ throwE $ "no such code: " ++ show funName

insTypeEnv :: Identifier -> WeakType -> WithEnv ()
insTypeEnv i t = modify (\e -> e {typeEnv = (i, t) : typeEnv e})

insTermEnv :: Identifier -> Term -> WithEnv ()
insTermEnv i t = modify (\e -> e {termEnv = (i, t) : termEnv e})

insPolTypeEnv :: Identifier -> Pos -> WithEnv ()
insPolTypeEnv i t = modify (\e -> e {polTypeEnv = (i, t) : polTypeEnv e})

insCodeEnv :: Identifier -> [Identifier] -> Code -> WithEnv ()
insCodeEnv funName args body =
  modify (\e -> e {codeEnv = (funName, (args, body)) : codeEnv e})

insConstraintEnv :: WeakType -> WeakType -> WithEnv ()
insConstraintEnv t1 t2 =
  modify (\e -> e {constraintEnv = (t1, t2) : constraintEnv e})

insEnumEnv :: Identifier -> [Identifier] -> WithEnv ()
insEnumEnv name labels = modify (\e -> e {enumEnv = (name, labels) : enumEnv e})

lookupEnumEnv' :: Identifier -> WithEnv [Identifier]
lookupEnumEnv' name = do
  mt <- gets (lookup name . enumEnv)
  case mt of
    Nothing -> lift $ throwE $ name ++ " is not found in the enum environment."
    Just t -> return t

lookupEnumKind' :: Identifier -> WithEnv Identifier
lookupEnumKind' name = do
  env <- get
  case findEnumKind name (enumEnv env) of
    Just x  -> return x
    Nothing -> lift $ throwE $ "the label " ++ name ++ " is not a defined."

findEnumKind :: Identifier -> [(Identifier, [Identifier])] -> Maybe Identifier
findEnumKind _ [] = Nothing
findEnumKind name ((cand, labelList):rest) =
  if name `elem` labelList
    then return cand
    else findEnumKind name rest

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

-- foldMR' ::
--      (a -> Cofree f Identifier -> f (Cofree f Identifier))
--   -> Cofree f Identifier
--   -> [a]
--   -> StateT Env (ExceptT String IO) (Cofree f Identifier)
-- foldMR _ e [] = return e
-- foldMR f e (t:ts) = do
--   tmp <- foldMR f e ts
--   let x = f t tmp
--   i <- newName
--   return $ i :< x
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
  undefined
  -- t <- lookupTypeEnv' i
  -- case t of
  --   _ :< NeutForall _ tcod -> do
  --     meta <- newNameWith "meta"
  --     insTypeEnv meta tcod
  --     appFold (meta :< NeutApp e term) ts
  --   _ -> error "Lift.appFold"

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
  undefined
  -- tLam <- lookupTypeEnv' metaLam
  -- tArg <- lookupTypeEnv' arg
  -- tmp <- bindFormalArgs xs c
  -- meta <- newNameWith "meta"
  -- univMeta <- newNameWith "meta"
  -- insTypeEnv univMeta (univMeta :< NeutUniv)
  -- insTypeEnv meta (univMeta :< NeutForall (arg, tArg) tLam)
  -- return $ meta :< NeutLam (arg, tArg) tmp

forallArgs :: Neut -> (Neut, [(Identifier, Neut, Identifier)])
forallArgs = undefined

-- forallArgs (meta :< NeutForall (i, vt) t) = do
--   let (body, xs) = forallArgs t
--   (body, (i, vt, meta) : xs)
-- forallArgs body = (body, [])
coForallArgs :: (Neut, [(Identifier, Neut, Identifier)]) -> Neut
coForallArgs (t, [])                 = t
coForallArgs (t, (i, tdom, meta):ts) = undefined
  -- coForallArgs (meta :< NeutForall (i, tdom) t, ts)

funAndArgs :: Neut -> WithEnv (Neut, [(Identifier, Neut)])
funAndArgs = undefined

-- funAndArgs (i :< NeutApp e v) = do
--   (fun, xs) <- funAndArgs e
--   return (fun, (i, v) : xs)
-- funAndArgs c = return (c, [])
coFunAndArgs :: (Neut, [(Identifier, Neut)]) -> Neut
coFunAndArgs = undefined

-- coFunAndArgs (term, [])        = term
-- coFunAndArgs (term, (i, v):xs) = coFunAndArgs (i :< NeutApp term v, xs)
var :: Neut -> [Identifier]
var = undefined

-- var (_ :< NeutVar s) = [s]
-- var (_ :< NeutForall (i, tdom) tcod) = var tdom ++ filter (/= i) (var tcod)
-- var (_ :< NeutLam (s, tdom) e) = var tdom ++ filter (/= s) (var e)
-- var (_ :< NeutApp e v) = var e ++ var v
-- var (_ :< NeutExists (i, tdom) tcod) = var tdom ++ filter (/= i) (var tcod)
-- var (_ :< NeutPair v1 v2) = var v1 ++ var v2
-- var (_ :< NeutCase e1 (x, y) e2) =
--   var e1 ++ filter (\s -> s /= x && s /= y) (var e2)
-- var (_ :< NeutTop) = []
-- var (_ :< NeutUnit) = []
-- var (_ :< NeutUniv) = []
-- var (_ :< NeutMu s e) = filter (/= s) (var e)
-- var (_ :< NeutHole _) = []
type Subst = [(Identifier, WeakType)]

subst :: Subst -> WeakType -> WeakType
subst = undefined

-- subst _ (j :< NeutVar s) = j :< NeutVar s
-- subst sub (j :< NeutForall (s, tdom) tcod) = do
--   let tdom' = subst sub tdom
--   let tcod' = subst sub tcod -- note that we don't have to drop s from sub, thanks to rename.
--   j :< NeutForall (s, tdom') tcod'
-- subst sub (j :< NeutLam (s, tdom) body) = do
--   let tdom' = subst sub tdom
--   let body' = subst sub body
--   j :< NeutLam (s, tdom') body'
-- subst sub (j :< NeutApp e1 e2) = do
--   let e1' = subst sub e1
--   let e2' = subst sub e2
--   j :< NeutApp e1' e2'
-- subst sub (j :< NeutExists (s, tdom) tcod) = do
--   let tdom' = subst sub tdom
--   let tcod' = subst sub tcod
--   j :< NeutExists (s, tdom') tcod'
-- subst sub (j :< NeutPair e1 e2) = do
--   let e1' = subst sub e1
--   let e2' = subst sub e2
--   j :< NeutPair e1' e2'
-- subst sub (j :< NeutCase e1 (x, y) e2) = do
--   let e1' = subst sub e1
--   let e2' = subst sub e2
--   j :< NeutCase e1' (x, y) e2'
-- subst _ (j :< NeutTop) = j :< NeutTop
-- subst _ (j :< NeutUnit) = j :< NeutUnit
-- subst _ (j :< NeutUniv) = j :< NeutUniv
-- subst sub (j :< NeutMu x e) = do
--   let e' = subst sub e
--   j :< NeutMu x e'
-- subst sub (j :< NeutHole s) = fromMaybe (j :< NeutHole s) (lookup s sub)
type SubstIdent = [(Identifier, Identifier)]

substIdent :: SubstIdent -> Identifier -> Identifier
substIdent sub x = fromMaybe x (lookup x sub)

substPos :: SubstIdent -> Pos -> Pos
substPos = undefined

-- substPos sub (Pos (j :< PosVar s)) = Pos $ j :< PosVar (substIdent sub s)
-- substPos sub (Pos (j :< PosForall (s, tdom) tcod)) = do
--   let Pos tdom' = substPos sub $ Pos tdom
--   let Pos tcod' = substPos sub $ Pos tcod
--   Pos $ j :< PosForall (s, tdom') tcod'
-- substPos sub (Pos (j :< PosExists (s, tdom) tcod)) = do
--   let Pos tdom' = substPos sub $ Pos tdom
--   let Pos tcod' = substPos sub $ Pos tcod
--   Pos $ j :< PosExists (s, tdom') tcod'
-- substPos sub (Pos (j :< PosPair x y)) = do
--   let x' = substIdent sub x
--   let y' = substIdent sub y
--   Pos $ j :< PosPair x' y'
-- substPos sub (Pos (j :< PosDown t)) = do
--   let Pos t' = substPos sub $ Pos t
--   Pos $ j :< PosDown t'
-- substPos sub (Pos (j :< PosThunkLam s body)) = do
--   let body' = substNeg sub body
--   Pos $ j :< PosThunkLam s body'
-- substPos sub (Pos (j :< PosUp t)) = do
--   let Pos t' = substPos sub $ Pos t
--   Pos $ j :< PosUp t'
-- substPos _ (Pos (j :< PosTop)) = Pos $ j :< PosTop
-- substPos _ (Pos (j :< PosUnit)) = Pos $ j :< PosUnit
-- substPos _ (Pos (j :< PosUniv)) = Pos $ j :< PosUniv
substNeg :: SubstIdent -> Neg -> Neg
substNeg sub (Neg (j :< NegArrowElimDownElim e vs)) = do
  let e' = substIdent sub e
  let vs' = map (substIdent sub) vs
  Neg $ j :< NegArrowElimDownElim e' vs'
substNeg sub (Neg (j :< NegProductElim v (x, y) e)) = do
  let v' = substIdent sub v
  let Neg e' = substNeg sub $ Neg e
  Neg $ j :< NegProductElim v' (x, y) e'
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
reduce = undefined

-- reduce (i :< NeutApp e1 e2) = do
--   let e2' = reduce e2
--   let e1' = reduce e1
--   case e1' of
--     _ :< NeutLam (arg, _) body -> do
--       let sub = [(arg, reduce e2)]
--       let _ :< body' = subst sub body
--       reduce $ i :< body'
--     _ -> i :< NeutApp e1' e2'
-- reduce (i :< NeutPair e1 e2) = do
--   let e1' = reduce e1
--   let e2' = reduce e2
--   i :< NeutPair e1' e2'
-- reduce (i :< NeutCase e (x, y) body) = do
--   let e' = reduce e
--   case e of
--     _ :< NeutPair e1 e2 -> do
--       let sub = [(x, reduce e1), (y, reduce e2)]
--       let _ :< body' = subst sub body
--       reduce $ i :< body'
--     _ -> i :< NeutCase e' (x, y) body
-- reduce (meta :< NeutMu s c) = do
--   let c' = reduce c
--   meta :< NeutMu s c'
-- reduce t = t
-- bindWithLet x e1 e2 ~> let x := e1 in e2
bindWithLet :: Identifier -> Neut -> Neut -> WithEnv Neut
bindWithLet x e1 e2 = do
  i <- newName
  j <- newName
  tdom <- lookupTypeEnv' x
  undefined
  -- return $ j :< NeutApp (i :< NeutLam (x, tdom) e2) e1

-- pendSubst :: Subst -> Neut -> WithEnv Neut
-- pendSubst [] e = return e
-- pendSubst ((x, e1):rest) e = do
--   e' <- pendSubst rest e
--   bindWithLet x e1 e'
-- wrap :: NeutF Neut -> WithEnv Neut
wrap :: f (Cofree f Identifier) -> WithEnv (Cofree f Identifier)
wrap a = do
  meta <- newNameWith "meta"
  return $ meta :< a

wrapType :: NeutF Neut -> WithEnv Neut
wrapType t = do
  meta <- newNameWith "meta"
  undefined
  -- u <- wrap NeutUniv
  -- insTypeEnv meta u
  -- return $ meta :< t

substItem :: Data -> [(Identifier, Data)] -> Identifier -> Data
substItem orig sub x = fromMaybe orig (lookup x sub)

substData :: [(Identifier, Data)] -> Data -> Data
substData sub (DataLocal x)   = substItem (DataLocal x) sub x
substData sub (DataGlobal x)  = substItem (DataGlobal x) sub x
substData _ DataNullPtr       = DataNullPtr
substData sub (DataStruct ds) = DataStruct $ map (substData sub) ds

substCode :: [(Identifier, Data)] -> Code -> Code
substCode sub (CodeReturn d) = CodeReturn $ substData sub d
substCode sub (CodeLet x d cont) =
  CodeLet x (substData sub d) (substCode sub cont)
substCode sub (CodeCall x fun args cont) =
  CodeCall x (substData sub fun) (map (substData sub) args) (substCode sub cont)
substCode sub (CodeExtractValue x d i cont) =
  CodeExtractValue x (substData sub d) i (substCode sub cont)
