module Parse
  ( parseType
  , parse
  , parseTypeArg
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

parse :: Tree -> WithEnv Term
parse (meta :< TreeAtom "_") = do
  name <- newNameWith "hole"
  return $ meta :< TermVar name
parse (meta :< TreeAtom s) = return $ meta :< TermVar s
parse (meta :< TreeNode [_ :< TreeAtom "thunk", te]) = do
  e <- parse te
  return $ meta :< TermThunk e
parse (meta :< TreeNode [_ :< TreeAtom "lambda", _ :< TreeNode ts, te]) = do
  xs <- parseIdentSeq ts
  e <- parse te
  _ :< term <- foldMTermR TermLam e xs
  return $ meta :< term
parse (meta :< TreeNode [_ :< TreeAtom "lift", tv]) = do
  v <- parse tv
  return $ meta :< TermLift v
parse (meta :< TreeNode [_ :< TreeAtom "colift", tv]) = do
  v <- parse tv
  return $ meta :< TermColift v
parse (meta :< TreeNode [_ :< TreeAtom "unthunk", tv]) = do
  v <- parse tv
  return $ meta :< TermUnthunk v
parse (meta :< TreeNode [_ :< TreeAtom "mu", _ :< TreeAtom s, te]) = do
  s' <- strToName s
  e <- parse te
  return $ meta :< TermMu s' e
parse (meta :< TreeNode ((_ :< TreeAtom "match"):(_ :< TreeNode tvs):tves))
  | not (null tves) = do
    vs <- mapM parse tvs
    ves <- mapM parseClause tves
    return $ meta :< TermCase vs ves
parse (meta :< TreeNode (te:tvs))
  | not (null tvs) = do
    e <- parse te
    vs <- mapM parse tvs
    _ :< tmp <- foldMTermL TermApp e vs
    return $ meta :< tmp
parse t = lift $ throwE $ "parse: syntax error:\n" ++ Pr.ppShow t

parseIdentSeq :: [Tree] -> WithEnv [Identifier]
parseIdentSeq [] = return []
parseIdentSeq ((_ :< TreeAtom s):ts) = do
  xs <- parseIdentSeq ts
  return $ s : xs
parseIdentSeq t =
  lift $ throwE $ "parseIdentSeq: syntax error:\n" ++ Pr.ppShow t

parsePat :: Tree -> WithEnv Pat
parsePat (meta :< TreeAtom "_") = do
  return $ meta :< PatHole
parsePat (meta :< TreeAtom s) = do
  msym <- lookupVEnv s
  case msym of
    Nothing -> do
      s' <- strToName s
      return (meta :< PatVar s')
    Just (s, _, _) -> return $ meta :< PatApp s []
parsePat (meta :< TreeNode ((_ :< TreeAtom s):ts)) = do
  msym <- lookupVEnv s
  case msym of
    Nothing ->
      lift $ throwE $ "parsePat: the constant " ++ show s ++ " is not defined"
    Just _ -> do
      ts' <- mapM parsePat ts
      return $ meta :< PatApp s ts'
parsePat t = lift $ throwE $ "parsePat: syntax error:\n" ++ Pr.ppShow t

parseClause :: Tree -> WithEnv ([Pat], Term)
parseClause (_ :< TreeNode [(_ :< TreeAtom "with"), (_ :< TreeNode tps), tbody]) = do
  ps <- mapM parsePat tps
  body <- parse tbody
  return (ps, body)
parseClause t = lift $ throwE $ "parseClause: syntax error:\n" ++ Pr.ppShow t

parseType :: Tree -> WithEnv Type
parseType (meta :< TreeAtom "_") = do
  name <- newNameWith "hole"
  return (meta :< TypeHole name)
parseType (meta :< TreeAtom "universe") = do
  t <- TypeUniv . WeakLevelHole <$> newName
  return $ meta :< t
parseType (meta :< TreeAtom s) = return $ meta :< TypeVar s -- ?
parseType (meta :< TreeNode [_ :< TreeAtom "down", tn]) = do
  n <- parseType tn
  return $ meta :< TypeDown n
parseType (meta :< TreeNode [_ :< TreeAtom "universe", _ :< TreeAtom si]) =
  case readMaybe si of
    Nothing -> lift $ throwE $ "not a number: " ++ si
    Just j  -> return $ meta :< TypeUniv (WeakLevelFixed j)
parseType (meta :< TreeNode [_ :< TreeAtom "forall", _ :< TreeNode ts, tn]) = do
  its <- mapM parseTypeArg ts
  n <- parseType tn
  _ :< t <- foldMTermR TypeForall n its
  return $ meta :< t
parseType (meta :< TreeNode [_ :< TreeAtom "up", tp]) = do
  p <- parseType tp
  return $ meta :< TypeUp p
parseType (meta :< TreeNode ((_ :< TreeAtom s):ts)) = do
  msym <- lookupVEnv s
  case msym of
    Nothing -> lift $ throwE $ "the constant " ++ show s ++ " is not defined"
    Just (s, args, _) -- "nat" should be written as `(nat)`, for example.
      | length args == length ts -> do
        es <- mapM parseType ts
        return $ meta :< TypeNode s es
    Just (s, args, _) -> do
      lift $
        throwE $
        "the arity of " ++
        show s ++ " is " ++ show (length args) ++ ", not " ++ show (length ts)
parseType t = lift $ throwE $ "parseType: syntax error:\n" ++ Pr.ppShow t

parseTypeArg :: Tree -> WithEnv (Identifier, Type)
parseTypeArg (_ :< TreeNode [_ :< TreeAtom s, tp]) = do
  s' <- strToName s
  t <- parseType tp
  return (s', t)
parseTypeArg t = lift $ throwE $ "parseTypeArg: syntax error:\n" ++ Pr.ppShow t

strToName :: String -> WithEnv Identifier
strToName "_" = newNameWith "hole"
strToName s   = return $ s
