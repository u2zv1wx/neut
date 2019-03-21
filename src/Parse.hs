-- This module translates an ordinary S-expression to corresponding AST.
-- The parsing here is more or less straightforward. One exception would be the
-- parseing of a term`(e1 e2 ... en)`, where `e1` is not a keyword.
-- We interpret this kind of terms as `(unbox e1) @ e2 @ ... @ en`. The heading
-- `unbox` might seem a little alien. In our type system, ordinary functions
-- have box types in normal circumstances. For example, a function that computes
-- the factorial of an integer value would have the type `box (i32 -> i32)`,
-- not `i32 -> i32`. Therefore, without the heading `unbox`, one might need to
-- write something like `((unbox fact) 100)` in every applications. That would
-- be cumbersome, and this is why we adopt this shorthand.
module Parse
  ( parse
  , parseAtom
  ) where

import Control.Monad (void)
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans.Except

import Control.Comonad.Cofree

import Data
import Util

import Data.List
import Data.Maybe

import Text.Read (readMaybe)

import qualified Text.Show.Pretty as Pr

parse :: Tree -> WithEnv Neut
parse (_ :< TreeNode [_ :< TreeAtom "forall", _ :< TreeNode ts, tn]) = do
  its <- mapM parseArg ts
  n <- parse tn
  foldMR NeutPi n its
parse (_ :< TreeNode ((_ :< TreeAtom "arrow"):ts)) = do
  typeList <- mapM parse ts
  let argList = take (length typeList - 1) typeList
  let cod = last typeList
  identList <- mapM (const $ newNameWith "hole") argList
  foldMR NeutPi cod $ zip identList argList
parse (meta :< TreeNode [_ :< TreeAtom "lambda", _ :< TreeNode ts, te]) = do
  xs <- mapM parseArg ts
  e <- parse te
  _ :< term <- foldMR NeutPiIntro e xs
  return $ meta :< term
parse (meta :< TreeNode [_ :< TreeAtom "apply", t1, t2]) = do
  e1 <- parse t1
  e2 <- parse t2
  return $ meta :< NeutPiElim e1 e2
parse (meta :< TreeNode [_ :< TreeAtom "exists", _ :< TreeNode ts, tn]) = do
  its <- mapM parseArg ts
  n <- parse tn
  i <- newNameWith "any"
  let xs = its ++ [(i, n)]
  return $ meta :< NeutSigma xs
parse (meta :< TreeNode ((_ :< TreeAtom "product"):ts)) = do
  typeList <- mapM parse ts
  let argList = take (length typeList - 1) typeList
  let rightMost = last typeList
  identList <- mapM (const $ newNameWith "hole") (argList ++ [rightMost])
  return $ meta :< NeutSigma (zip identList (argList ++ [rightMost]))
parse (meta :< TreeNode ((_ :< TreeAtom "pair"):ts)) = do
  es <- mapM parse ts
  return $ meta :< NeutSigmaIntro es
parse (meta :< TreeNode [_ :< TreeAtom "case", t, _ :< TreeNode [_ :< TreeNode ((_ :< TreeAtom "pair"):ts), tbody]]) = do
  e <- parse t
  tmp <- mapM parseArg ts
  let args = map fst tmp
  body <- parse tbody
  return $ meta :< NeutSigmaElim e args body
parse (meta :< TreeNode [_ :< TreeAtom "case", t, _ :< TreeNode ts]) = do
  e <- parse t
  branchList <- mapM parseClause ts
  return $ meta :< NeutIndexElim e branchList
parse (meta :< TreeAtom "universe") = do
  hole <- newNameWith "univ"
  return $ meta :< NeutUniv (UnivLevelHole hole)
parse (meta :< TreeNode [_ :< TreeAtom "mu", _ :< TreeAtom x, te]) = do
  e <- parse te
  return $ meta :< NeutMu x e
parse (meta :< TreeNode (te:tvs)) = do
  e <- parse te
  vs <- mapM parse tvs
  _ :< tmp <- foldML NeutPiElim e vs
  return $ meta :< tmp
parse (meta :< TreeAtom "_") = do
  name <- newNameWith "hole"
  return $ meta :< NeutHole name
parse (meta :< TreeAtom s)
  | '.' `elem` s
  , Just f <- readMaybe s = return $ meta :< NeutIndexIntro (IndexFloat f)
  | Just i <- readMaybe s = return $ meta :< NeutIndexIntro (IndexInteger i)
parse (meta :< TreeAtom s) = do
  flag1 <- isDefinedIndex s
  flag2 <- isDefinedIndexName s
  flag3 <- lookupNameEnv'' s
  case (flag1, flag2, flag3) of
    (True, False, _) -> return $ meta :< NeutIndexIntro (IndexLabel s)
    (False, True, _) -> return $ meta :< NeutIndex s
    (_, _, Just s') -> return $ meta :< NeutConst s'
    (_, _, Nothing) -> return $ meta :< NeutVar s
parse t = lift $ throwE $ "parse: syntax error:\n" ++ Pr.ppShow t

parseClause :: Tree -> WithEnv (IndexOrVar, Neut)
parseClause (_ :< TreeNode [_ :< TreeAtom s, t])
  | '.' `elem` s
  , Just f <- readMaybe s = do
    e <- parse t
    return (Left $ IndexFloat f, e)
parseClause (_ :< TreeNode [_ :< TreeAtom s, t])
  | Just i <- readMaybe s = do
    e <- parse t
    return (Left $ IndexInteger i, e)
parseClause (_ :< TreeNode [_ :< TreeAtom "default", t]) = do
  e <- parse t
  return (Left IndexDefault, e)
parseClause (_ :< TreeNode [_ :< TreeAtom s, t]) = do
  e <- parse t
  b <- isDefinedIndex s
  if b
    then return (Left $ IndexLabel s, e)
    else return (Right s, e)
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
