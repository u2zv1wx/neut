module Parse
  ( parse
  , parseType
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
parse (meta :< TreeNode [_ :< TreeAtom "lambda", _ :< TreeNode ts, te]) = do
  xs <- mapM parseArg ts
  e <- parse te
  _ :< term <- foldMR NeutArrowIntro e xs
  return $ meta :< term
parse (meta :< TreeNode [_ :< TreeAtom "forall", _ :< TreeNode ts, te]) = do
  xs <- mapM parseTypeArg ts
  e <- parse te
  _ :< term <- foldMR NeutForallIntro e xs
  return $ meta :< term
parse (meta :< TreeNode [_ :< TreeAtom "instance", t1, t2]) = do
  e1 <- parse t1
  t <- parseType t2
  return $ meta :< NeutForallElim e1 t
parse (meta :< TreeNode [_ :< TreeAtom "struct", _ :< TreeNode ts]) = do
  xs <- mapM parseStructArg ts
  return $ meta :< NeutPiIntro xs
parse (meta :< TreeNode [_ :< TreeAtom "project", t1, t2]) = do
  e1 <- parse t1
  e2 <- parse t2
  return $ meta :< NeutPiElim e1 e2
parse (meta :< TreeNode [_ :< TreeAtom "pair", t1, t2]) = do
  e1 <- parse t1
  e2 <- parse t2
  return $ meta :< NeutProductIntro e1 e2
parse (meta :< TreeNode [_ :< TreeAtom "case", t, _ :< TreeNode [_ :< TreeAtom "pair", _ :< TreeAtom x, _ :< TreeAtom y], tbody]) = do
  e <- parse t
  body <- parse tbody
  return $ meta :< NeutProductElim e (x, y) body
parse (meta :< TreeNode [_ :< TreeAtom "exists", _ :< TreeNode ts, te]) = do
  xs <- mapM parseTypeArg ts
  e <- parse te
  _ :< term <- foldMR NeutExistsIntro e xs
  return $ meta :< term
parse (meta :< TreeNode [_ :< TreeAtom "case", t, _ :< TreeNode [_ :< TreeAtom "exists", _ :< TreeAtom x, _ :< TreeAtom y], tbody]) = do
  e <- parse t
  body <- parse tbody
  return $ meta :< NeutExistsElim e (x, y) body
parse (meta :< TreeNode [_ :< TreeAtom "inject", t1, t2]) = do
  e1 <- parse t1
  e2 <- parse t2
  return $ meta :< NeutSigmaIntro e1 e2
parse (meta :< TreeNode [_ :< TreeAtom "case", t, _ :< TreeNode clauseList]) = do
  e <- parse t
  cs <- mapM parseClause clauseList
  return $ meta :< NeutSigmaElim e cs
parse (meta :< TreeAtom "unit") = return $ meta :< NeutTopIntro
parse (meta :< TreeNode [_ :< TreeAtom "mu", _ :< TreeAtom x, te]) = do
  e <- parse te
  return $ meta :< NeutMu x e
parse (meta :< TreeNode (te:tvs))
  | not (null tvs) = do
    e <- parse te
    vs <- mapM parse tvs
    _ :< tmp <- foldML NeutArrowElim e vs
    return $ meta :< tmp
parse (meta :< TreeAtom s) = return $ meta :< NeutVar s
parse t = lift $ throwE $ "parse: syntax error:\n" ++ Pr.ppShow t

parseClause :: Tree -> WithEnv ((Identifier, Identifier), Neut)
parseClause (_ :< TreeNode [_ :< TreeNode [_ :< TreeAtom "inject", _ :< TreeAtom x, _ :< TreeAtom y], tbody]) = do
  body <- parse tbody
  return ((x, y), body)
parseClause t = lift $ throwE $ "parseClause: syntax error:\n" ++ Pr.ppShow t

parseType :: Tree -> WithEnv WeakType
parseType (_ :< TreeNode ((_ :< TreeAtom "arrow"):ts)) = do
  typeList <- mapM parseType ts
  foldArrow typeList
parseType (_ :< TreeNode [_ :< TreeAtom "forall", _ :< TreeNode ts, tn]) = do
  its <- mapM parseTypeArg ts
  n <- parseType tn
  return $ foldr WeakTypeForall n its
parseType (_ :< TreeNode [_ :< TreeAtom "pi", _ :< TreeNode ts]) = do
  xs <- mapM parseArg ts
  return $ WeakTypePi xs
parseType (_ :< TreeNode ((_ :< TreeAtom "product"):ts)) = do
  typeList <- mapM parseType ts
  foldProduct typeList
parseType (_ :< TreeNode [_ :< TreeAtom "exists", _ :< TreeNode ts, tn]) = do
  its <- mapM parseTypeArg ts
  n <- parseType tn
  return $ foldr WeakTypeExists n its
parseType (_ :< TreeNode [_ :< TreeAtom "sigma", _ :< TreeNode ts]) = do
  xs <- mapM parseArg ts
  return $ WeakTypeSigma xs
parseType (_ :< TreeAtom "top") = return WeakTypeTop
parseType (_ :< TreeAtom "_") = do
  name <- newNameWith "hole"
  return $ WeakTypeHole name
parseType (_ :< TreeAtom s) = return $ WeakTypeVar s
parseType t = lift $ throwE $ "parseType: syntax error:\n" ++ Pr.ppShow t

foldArrow :: [WeakType] -> WithEnv WeakType
foldArrow []         = lift $ throwE "foldArrow: syntax error"
foldArrow [_]        = lift $ throwE "foldArrow: syntax error"
foldArrow [dom, cod] = return $ WeakTypeArrow dom cod
foldArrow (dom:rest) = WeakTypeArrow dom <$> foldArrow rest

foldProduct :: [WeakType] -> WithEnv WeakType
foldProduct []             = lift $ throwE "foldProduct: syntax error"
foldProduct [_]            = lift $ throwE "foldProduct: syntax error"
foldProduct [dom, cod]     = return $ WeakTypeProduct dom cod
foldProduct (dom:cod:rest) = foldProduct $ WeakTypeProduct dom cod : rest

parseArg :: Tree -> WithEnv (Identifier, WeakType)
parseArg (_ :< TreeAtom s) = do
  i <- newNameWith "any"
  return (s, WeakTypeHole i)
parseArg (_ :< TreeNode [targ, tp]) = do
  (arg, _) <- parseArg targ
  t <- parseType tp
  return (arg, t)
parseArg t = lift $ throwE $ "parseArg: syntax error:\n" ++ Pr.ppShow t

parseStructArg :: Tree -> WithEnv (Identifier, Neut)
parseStructArg (_ :< TreeNode [_ :< TreeAtom s, tp]) = do
  e <- parse tp
  return (s, e)
parseStructArg t =
  lift $ throwE $ "parseStructArg: syntax error:\n" ++ Pr.ppShow t

parseTypeArg :: Tree -> WithEnv Identifier
parseTypeArg (_ :< TreeAtom s) = return s
parseTypeArg t = lift $ throwE $ "parseTypeArg: syntax error:\n" ++ Pr.ppShow t
