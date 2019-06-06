-- This module translates an ordinary S-expression to corresponding AST.
-- The parsing here is more or less straightforward. One exception would be the
-- interpreting of a term`(e1 e2 ... en)`, where `e1` is not a keyword.
-- We interpret this kind of terms as `(unbox e1) @ e2 @ ... @ en`. The heading
-- `unbox` might seem a little alien. In our type system, ordinary functions
-- have box types in normal circumstances. For example, a function that computes
-- the factorial of an integer value would have the type `box (i32 -> i32)`,
-- not `i32 -> i32`. Therefore, without the heading `unbox`, one might need to
-- write something like `((unbox fact) 100)` in every applications. That would
-- be cumbersome, and this is why we adopt this shorthand.
module Parse.Interpret
  ( interpret
  , interpretAtom
  ) where

import           Control.Comonad.Cofree
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Text.Read                  (readMaybe)
import qualified Text.Show.Pretty           as Pr

import           Data.Basic
import           Data.Env
import           Data.Neut
import           Data.Tree
import           Util

interpret :: Tree -> WithEnv Neut
interpret (_ :< TreeNode [_ :< TreeAtom "forall", _ :< TreeNode ts, tn]) = do
  its <- mapM interpretArg ts
  n <- interpret tn
  foldMR NeutPi n its
interpret (_ :< TreeNode ((_ :< TreeAtom "arrow"):ts)) = do
  typeList <- mapM interpret ts
  let argList = take (length typeList - 1) typeList
  let cod = last typeList
  identList <- mapM (const $ newNameWith "hole") argList
  foldMR NeutPi cod $ zip identList argList
interpret (meta :< TreeNode [_ :< TreeAtom "lambda", _ :< TreeNode ts, te]) = do
  xs <- mapM interpretArg ts
  e <- interpret te
  _ :< term <- foldMR NeutPiIntro e xs
  return $ meta :< term
interpret (meta :< TreeNode [_ :< TreeAtom "apply", t1, t2]) = do
  e1 <- interpret t1
  e2 <- interpret t2
  return $ meta :< NeutPiElim e1 e2
interpret (meta :< TreeNode [_ :< TreeAtom "exists", _ :< TreeNode ts, tn]) = do
  its <- mapM interpretArg ts
  n <- interpret tn
  i <- newNameWith "any"
  let xs = its ++ [(i, n)]
  return $ meta :< NeutSigma xs
interpret (meta :< TreeNode ((_ :< TreeAtom "product"):ts)) = do
  typeList <- mapM interpret ts
  let argList = take (length typeList - 1) typeList
  let rightMost = last typeList
  identList <- mapM (const $ newNameWith "hole") (argList ++ [rightMost])
  return $ meta :< NeutSigma (zip identList (argList ++ [rightMost]))
interpret (meta :< TreeNode ((_ :< TreeAtom "pair"):ts)) = do
  es <- mapM interpret ts
  return $ meta :< NeutSigmaIntro es
interpret (meta :< TreeNode [_ :< TreeAtom "case", t, _ :< TreeNode [_ :< TreeNode ((_ :< TreeAtom "pair"):ts), tbody]]) = do
  e <- interpret t
  tmp <- mapM interpretArg ts
  let args = map fst tmp
  body <- interpret tbody
  return $ meta :< NeutSigmaElim e args body
interpret (meta :< TreeNode [_ :< TreeAtom "case", t, _ :< TreeNode ts]) = do
  e <- interpret t
  branchList <- mapM interpretClause ts
  return $ meta :< NeutIndexElim e branchList
interpret (meta :< TreeAtom "universe") = do
  hole <- newNameWith "univ"
  return $ meta :< NeutUniv (UnivLevelHole hole)
interpret (meta :< TreeNode [_ :< TreeAtom "mu", _ :< TreeAtom x, te]) = do
  e <- interpret te
  return $ meta :< NeutMu x e
interpret (meta :< TreeNode (te:tvs)) = do
  e <- interpret te
  vs <- mapM interpret tvs
  _ :< tmp <- foldML NeutPiElim e vs
  return $ meta :< tmp
interpret (meta :< TreeAtom "_") = do
  name <- newNameWith "hole"
  return $ meta :< NeutHole name
interpret (meta :< TreeAtom s)
  | '.' `elem` s
  , Just f <- readMaybe s = return $ meta :< NeutIndexIntro (IndexFloat f)
  | Just i <- readMaybe s = return $ meta :< NeutIndexIntro (IndexInteger i)
interpret (meta :< TreeAtom s) = do
  flag1 <- isDefinedIndex s
  flag2 <- isDefinedIndexName s
  cenv <- gets constantEnv
  let flag3 = s `elem` cenv
  case (flag1, flag2, flag3) of
    (True, False, _) -> return $ meta :< NeutIndexIntro (IndexLabel s)
    (False, True, _) -> return $ meta :< NeutIndex s
    (_, _, False)    -> return $ meta :< NeutVar s
    (_, _, True)     -> return $ meta :< NeutConst s
interpret t = lift $ throwE $ "interpret: syntax error:\n" ++ Pr.ppShow t

interpretClause :: Tree -> WithEnv (Index, Neut)
interpretClause (_ :< TreeNode [_ :< TreeAtom s, t])
  | '.' `elem` s
  , Just f <- readMaybe s = do
    e <- interpret t
    return (IndexFloat f, e)
interpretClause (_ :< TreeNode [_ :< TreeAtom s, t])
  | Just i <- readMaybe s = do
    e <- interpret t
    return (IndexInteger i, e)
interpretClause (_ :< TreeNode [_ :< TreeAtom "_", t]) = do
  e <- interpret t
  return (IndexDefault, e)
interpretClause (_ :< TreeNode [_ :< TreeAtom s, t]) = do
  e <- interpret t
  b <- isDefinedIndex s
  if b
    then return (IndexLabel s, e)
    else lift $ throwE $ "no such label defined: " ++ s
interpretClause e =
  lift $ throwE $ "interpretClause: syntax error:\n " ++ Pr.ppShow e

interpretArg :: Tree -> WithEnv (Identifier, Neut)
interpretArg (meta :< TreeAtom s) = do
  i <- newNameWith "any"
  return (s, meta :< NeutHole i)
interpretArg (_ :< TreeNode [targ, tp]) = do
  (arg, _) <- interpretArg targ
  t <- interpret tp
  return (arg, t)
interpretArg t = lift $ throwE $ "interpretArg: syntax error:\n" ++ Pr.ppShow t

interpretAtom :: Tree -> WithEnv Identifier
interpretAtom (_ :< TreeAtom s) = return s
interpretAtom t =
  lift $ throwE $ "interpretAtom: syntax error:\n" ++ Pr.ppShow t
