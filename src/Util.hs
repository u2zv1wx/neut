module Util where

import           Control.Monad.Except
import           Control.Monad.Identity

import           Control.Comonad
import           Control.Comonad.Cofree

import           Control.Monad.State

import           Data

toPiIntroSeq :: Neut -> (Neut, [(Identifier, Neut, Identifier)])
toPiIntroSeq (meta :< NeutPiIntro (x, t) body) = do
  let (body', args) = toPiIntroSeq body
  (body', (x, t, meta) : args)
toPiIntroSeq t = (t, [])

fromPiIntroSeq :: (Neut, [(Identifier, Neut, Identifier)]) -> Neut
fromPiIntroSeq (e, []) = e
fromPiIntroSeq (e, (x, t, meta):rest) =
  fromPiIntroSeq (meta :< NeutPiIntro (x, t) e, rest)

toPiElimSeq :: Neut -> (Neut, [(Identifier, Neut)])
toPiElimSeq (i :< NeutPiElim e1 e2) = do
  let (fun, xs) = toPiElimSeq e1
  (fun, (i, e2) : xs)
toPiElimSeq c = (c, [])

fromPiElimSeq :: (Neut, [(Identifier, Neut)]) -> Neut
fromPiElimSeq (term, [])        = term
fromPiElimSeq (term, (i, v):xs) = fromPiElimSeq (i :< NeutPiElim term v, xs)

toPiSeq :: Neut -> (Neut, [(Identifier, Neut)])
toPiSeq (_ :< NeutPi (x, t) body) = do
  let (body', args) = toPiSeq body
  (body', (x, t) : args)
toPiSeq t = (t, [])

var :: Neut -> WithEnv [Identifier]
var (_ :< NeutVar s) = do
  b <- isExternalConst s
  if b
    then return []
    else return [s]
var (_ :< NeutPi (i, tdom) tcod) = do
  vs1 <- var tdom
  vs2 <- var tcod
  return $ vs1 ++ filter (/= i) vs2
var (_ :< NeutPiIntro (s, _) e) = do
  vs <- var e
  return $ filter (/= s) vs
var (_ :< NeutPiElim e1 e2) = do
  vs1 <- var e1
  vs2 <- var e2
  return $ vs1 ++ vs2
var (_ :< NeutSigma [] t2) = var t2
var (i :< NeutSigma ((x, t):xts) t2) = do
  vs1 <- var (i :< NeutSigma xts t2)
  vs2 <- var t
  return $ vs2 ++ filter (/= x) vs1
var (_ :< NeutSigmaIntro es) = join <$> mapM var es
var (_ :< NeutSigmaElim e1 xs e2) = do
  vs1 <- var e1
  vs2 <- var e2
  return $ vs1 ++ filter (`notElem` xs) vs2
var (_ :< NeutBox e) = var e
var (_ :< NeutBoxIntro e) = var e
var (_ :< NeutBoxElim e) = var e
var (_ :< NeutIndex _) = return []
var (_ :< NeutIndexIntro _) = return []
var (_ :< NeutIndexElim e branchList) = do
  vs <- var e
  let (_, es) = unzip branchList
  vss <- mapM var es
  return $ vs ++ join vss
var (_ :< NeutUniv _) = return []
var (_ :< NeutMu s e) = do
  vs <- var e
  return $ filter (/= s) vs
var (_ :< NeutHole _) = return []

var' :: Neut -> WithEnv [Identifier]
var' (_ :< NeutVar s) = do
  b <- isExternalConst s
  if b
    then return []
    else return [s]
var' (_ :< NeutPi (_, tdom) tcod) = do
  vs1 <- var' tdom
  vs2 <- var' tcod
  return $ vs1 ++ vs2
var' (_ :< NeutPiIntro (_, _) e) = var' e
var' (_ :< NeutPiElim e1 e2) = do
  vs1 <- var' e1
  vs2 <- var' e2
  return $ vs1 ++ vs2
var' (_ :< NeutSigma [] t2) = var' t2
var' (i :< NeutSigma ((x, t):xts) t2) = do
  vs1 <- var' (i :< NeutSigma xts t2)
  vs2 <- var' t
  return $ vs2 ++ filter (/= x) vs1
var' (_ :< NeutSigmaIntro es) = join <$> mapM var' es
var' (_ :< NeutSigmaElim e1 _ e2) = do
  vs1 <- var' e1
  vs2 <- var' e2
  return $ vs1 ++ vs2
var' (_ :< NeutBox e) = var' e
var' (_ :< NeutBoxIntro e) = var' e
var' (_ :< NeutBoxElim e) = var' e
var' (_ :< NeutIndex _) = return []
var' (_ :< NeutIndexIntro _) = return []
var' (_ :< NeutIndexElim e branchList) = do
  vs <- var' e
  let (_, es) = unzip branchList
  vss <- mapM var' es
  return $ vs ++ join vss
var' (_ :< NeutUniv _) = return []
var' (_ :< NeutMu _ e) = var' e
var' (_ :< NeutHole _) = return []

(+-+) ::
     ([Identifier], [Identifier])
  -> ([Identifier], [Identifier])
  -> ([Identifier], [Identifier])
(xs1, xs2) +-+ (ys1, ys2) = (xs1 ++ ys1, xs2 ++ ys2)

-- list all the variables and the metavariables in given term, assuming that
-- the term is renamed by `rename`
varAndHole :: Neut -> WithEnv ([Identifier], [Identifier])
varAndHole (_ :< NeutVar s) = do
  b <- isExternalConst s
  if b
    then return ([], [])
    else return ([s], [])
varAndHole (_ :< NeutPi (_, tdom) tcod) = do
  vs1 <- varAndHole tdom
  vs2 <- varAndHole tcod
  return $ vs1 +-+ vs2
varAndHole (_ :< NeutPiIntro _ e) = varAndHole e
varAndHole (_ :< NeutPiElim e1 e2) = do
  vs1 <- varAndHole e1
  vs2 <- varAndHole e2
  return $ vs1 +-+ vs2
varAndHole (_ :< NeutSigma [] t2) = varAndHole t2
varAndHole (i :< NeutSigma ((_, t):xts) t2) = do
  vs1 <- varAndHole (i :< NeutSigma xts t2)
  vs2 <- varAndHole t
  return $ vs1 +-+ vs2
varAndHole (_ :< NeutSigmaIntro es) = pairwiseConcat <$> mapM varAndHole es
varAndHole (_ :< NeutSigmaElim e1 _ e2) = do
  vs1 <- varAndHole e1
  vs2 <- varAndHole e2
  return $ vs1 +-+ vs2
varAndHole (_ :< NeutBox e) = varAndHole e
varAndHole (_ :< NeutBoxIntro e) = varAndHole e
varAndHole (_ :< NeutBoxElim e) = varAndHole e
varAndHole (_ :< NeutIndex _) = return ([], [])
varAndHole (_ :< NeutIndexIntro _) = return ([], [])
varAndHole (_ :< NeutIndexElim e branchList) = do
  vs <- varAndHole e
  let (_, es) = unzip branchList
  vss <- mapM varAndHole es
  return $ vs +-+ pairwiseConcat vss
varAndHole (_ :< NeutUniv _) = return ([], [])
varAndHole (_ :< NeutMu _ e) = varAndHole e
varAndHole (_ :< NeutHole x) = return ([], [x])

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

pairwiseConcat :: [([a], [b])] -> ([a], [b])
pairwiseConcat [] = ([], [])
pairwiseConcat ((xs, ys):rest) = do
  let (xs', ys') = pairwiseConcat rest
  (xs ++ xs', ys ++ ys')
