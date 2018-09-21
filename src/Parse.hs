module Parse
  ( parse
  , parseAtom
  ) where

import           Control.Monad              (void)
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Control.Comonad.Cofree

import           Data
import           Data.List
import           Data.Maybe

import           Text.Read                  (readMaybe)

import qualified Text.Show.Pretty           as Pr

parse :: Tree -> WithEnv Neut
parse (_ :< TreeNode [_ :< TreeAtom "forall", _ :< TreeNode ts, tn]) = do
  its <- mapM parseArg ts
  n <- parse tn
  foldMR NeutPi n its
parse (meta :< TreeNode [_ :< TreeAtom "lambda", _ :< TreeNode ts, te]) = do
  xs <- mapM parseArg ts
  e <- parse te
  _ :< term <- foldMR NeutPiIntro e xs
  return $ meta :< term
parse (_ :< TreeNode [_ :< TreeAtom "exists", _ :< TreeNode ts, tn]) = do
  its <- mapM parseArg ts
  n <- parse tn
  foldMR NeutSigma n its
parse (meta :< TreeNode [_ :< TreeAtom "pair", t1, t2]) = do
  e1 <- parse t1
  e2 <- parse t2
  return $ meta :< NeutSigmaIntro e1 e2
parse (meta :< TreeNode [_ :< TreeAtom "case", t, _ :< TreeNode [_ :< TreeAtom "pair", _ :< TreeAtom x, _ :< TreeAtom y], tbody]) = do
  e <- parse t
  body <- parse tbody
  return $ meta :< NeutSigmaElim e (x, y) body
parse (meta :< TreeNode [_ :< TreeAtom "case", t, _ :< TreeNode ts]) = do
  e <- parse t
  branchList <- mapM parseClause ts
  return $ meta :< NeutIndexElim e branchList
parse (meta :< TreeAtom "universe") = do
  hole <- newName
  return $ meta :< NeutUniv (UnivLevelHole hole)
parse (meta :< TreeNode [_ :< TreeAtom "mu", _ :< TreeAtom x, te]) = do
  e <- parse te
  return $ meta :< NeutMu x e
parse (meta :< TreeNode (te:tvs))
  | not (null tvs) = do
    e <- parse te
    vs <- mapM parse tvs
    _ :< tmp <- foldML NeutPiElim e vs
    return $ meta :< tmp
parse (meta :< TreeAtom "_") = do
  name <- newNameWith "hole"
  return $ meta :< NeutHole name
parse (meta :< TreeAtom s) = do
  flag <- isDefinedIndex s
  if flag
    then return $ meta :< NeutIndexIntro s
    else return $ meta :< NeutVar s
parse t = lift $ throwE $ "parse: syntax error:\n" ++ Pr.ppShow t

parseClause :: Tree -> WithEnv (Identifier, Neut)
parseClause (_ :< TreeNode [_ :< TreeAtom x, t]) = do
  e <- parse t
  return (x, e)
parseClause e = lift $ throwE $ "parseClause: syntax error:\n " ++ Pr.ppShow e

parseArg :: Tree -> WithEnv (Identifier, Neut)
parseArg (meta :< TreeAtom s) = do
  i <- newNameWith "any"
  return (s, meta :< NeutHole i)
parseArg (_ :< TreeNode [targ, tp]) = do
  (arg, _) <- parseArg targ
  t <- parse tp
  return (arg, t)
parseArg t = lift $ throwE $ "parseArg: syntax error:\n" ++ Pr.ppShow t

parseAtom :: Tree -> WithEnv Identifier
parseAtom (_ :< TreeAtom s) = return s
parseAtom t = lift $ throwE $ "parseAtom: syntax error:\n" ++ Pr.ppShow t
