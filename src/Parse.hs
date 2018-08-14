module Parse
  ( parseType
  , parseTerm
  , parseNodeTypeArg
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

parseTerm :: Tree -> WithEnv WeakTerm
parseTerm (meta :< TreeAtom "_") = do
  name <- newNameWith "hole"
  return (meta :< WeakTermVar name)
parseTerm (meta :< TreeAtom s) = return (meta :< WeakTermVar s)
parseTerm (meta :< TreeNode [_ :< TreeAtom "thunk", te]) = do
  e <- parseTerm te
  return (meta :< WeakTermThunk e)
parseTerm (meta :< TreeNode [_ :< TreeAtom "lambda", _ :< TreeNode ts, te]) = do
  xs <- parseIdentSeq ts
  e <- parseTerm te
  _ :< term <- foldMTermR WeakTermLam e xs
  return $ meta :< term
parseTerm (meta :< TreeNode [_ :< TreeAtom "return", tv]) = do
  v <- parseTerm tv
  return (meta :< WeakTermRet v)
parseTerm (meta :< TreeNode [_ :< TreeAtom "bind", _ :< TreeAtom s, te1, te2]) = do
  s' <- strOrNewName s
  e1 <- parseTerm te1
  e2 <- parseTerm te2
  return (meta :< WeakTermBind s' e1 e2)
parseTerm (meta :< TreeNode [_ :< TreeAtom "unthunk", tv]) = do
  v <- parseTerm tv
  return (meta :< WeakTermUnthunk v)
parseTerm (meta :< TreeNode [_ :< TreeAtom "mu", _ :< TreeAtom s, te]) = do
  s' <- strOrNewName s
  e <- parseTerm te
  return (meta :< WeakTermMu s' e)
parseTerm (meta :< TreeNode ((_ :< TreeAtom "match"):(_ :< TreeNode tvs):tves))
  | not (null tves) = do
    vs <- mapM parseTerm tvs
    ves <- mapM parseClause tves
    return (meta :< WeakTermCase vs ves)
parseTerm (meta :< TreeNode [_ :< TreeAtom "ascribe", te, tn]) = do
  e <- parseTerm te
  n <- parseType tn
  return (meta :< WeakTermAsc e n)
parseTerm (meta :< TreeNode (te@(_ :< TreeAtom s):ts)) = do
  msym <- lookupVEnv s
  case msym of
    Nothing -> parseTermApp te ts
    Just (s, args, _) -- "zero" should be written as `(zero)`, for example.
      | length args == length ts -> do
        es <- mapM parseTerm ts
        return $ meta :< WeakTermNodeApp s es
    Just (s, args, _) -> do
      lift $
        throwE $
        "the arity of " ++
        show s ++ " is " ++ show (length args) ++ ", not " ++ show (length ts)
parseTerm (_ :< TreeNode (te:tvs))
  | not (null tvs) = parseTermApp te tvs
parseTerm t = lift $ throwE $ "parseTerm: syntax error:\n" ++ Pr.ppShow t

parseTermApp :: Tree -> [Tree] -> WithEnv WeakTerm
parseTermApp te tvs = do
  e <- parseTerm te
  vs <- mapM parseTerm tvs
  foldMTerm WeakTermApp e vs

parseTermNodeApp :: Meta -> Identifier -> [Tree] -> WithEnv WeakTerm
parseTermNodeApp meta s tvs = do
  vs <- mapM parseTerm tvs
  return $ meta :< WeakTermNodeApp s vs
  -- foldMTerm WeakTermNodeApp e vs

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
      s' <- strOrNewName s
      return (meta :< PatVar s')
    Just (s, _, _) -> return (meta :< PatApp s [])
parsePat (meta :< TreeNode ((_ :< TreeAtom s):ts)) = do
  msym <- lookupVEnv s
  case msym of
    Nothing ->
      lift $ throwE $ "parsePat: the constant " ++ show s ++ " is not defined"
    Just _ -> do
      ts' <- mapM parsePat ts
      return $ meta :< PatApp s ts'
parsePat t = lift $ throwE $ "parsePat: syntax error:\n" ++ Pr.ppShow t

parseClause :: Tree -> WithEnv ([Pat], WeakTerm)
parseClause (_ :< TreeNode [(_ :< TreeAtom "with"), (_ :< TreeNode tps), tbody]) = do
  ps <- mapM parsePat tps
  body <- parseTerm tbody
  return (ps, body)
parseClause t = lift $ throwE $ "parseClause: syntax error:\n" ++ Pr.ppShow t

parseType :: Tree -> WithEnv WeakType
parseType (_ :< TreeAtom "_") = do
  name <- newNameWith "hole"
  return (WeakTypePosHole name)
parseType (_ :< TreeAtom "universe") = WeakTypeUniv . WeakLevelHole <$> newName
parseType (_ :< TreeAtom s) = return $ WeakTypeVar s
parseType (Meta {ident = i} :< TreeNode [_ :< TreeAtom "down", tn]) = do
  n <- parseType tn
  return $ WeakTypeDown n i
parseType (_ :< TreeNode [_ :< TreeAtom "universe", _ :< TreeAtom si]) =
  case readMaybe si of
    Nothing -> lift $ throwE $ "not a number: " ++ si
    Just j  -> return $ WeakTypeUniv (WeakLevelFixed j)
parseType (_ :< TreeNode [_ :< TreeAtom "forall", _ :< TreeNode ts, tn]) = do
  its <- mapM parseTypeArg ts
  n <- parseType tn
  return $ foldr WeakTypeForall n its
parseType (_ :< TreeNode [_ :< TreeAtom "up", tp]) = do
  p <- parseType tp
  return $ WeakTypeUp p
parseType (_ :< TreeNode ((_ :< TreeAtom s):ts)) = do
  msym <- lookupVEnv s
  case msym of
    Nothing -> lift $ throwE $ "the constant " ++ show s ++ " is not defined"
    Just (s, args, _) -- "nat" should be written as `(nat)`, for example.
      | length args == length ts -> do
        es <- mapM parseType ts
        return $ WeakTypeNode s es
    Just (s, args, _) -> do
      lift $
        throwE $
        "the arity of " ++
        show s ++ " is " ++ show (length args) ++ ", not " ++ show (length ts)
parseType t = lift $ throwE $ "parseType: syntax error:\n" ++ Pr.ppShow t

parseTypeArg :: Tree -> WithEnv (IdentOrHole, WeakType)
parseTypeArg (_ :< TreeNode [_ :< TreeAtom s, tp]) = do
  s' <- strToName s
  t <- parseType tp
  return (s', t)
parseTypeArg t = lift $ throwE $ "parseTypeArg: syntax error:\n" ++ Pr.ppShow t

parseNodeTypeArg :: Tree -> WithEnv (Identifier, WeakType)
parseNodeTypeArg (_ :< TreeNode [_ :< TreeAtom s, tp]) = do
  s' <- strOrNewName s
  t <- parseType tp
  return (s', t)
parseNodeTypeArg t =
  lift $ throwE $ "parseTypeArg: syntax error:\n" ++ Pr.ppShow t

strToName :: String -> WithEnv IdentOrHole
strToName "_" = do
  s <- newNameWith "hole"
  return $ Hole s
strToName s = return $ Ident s

strOrNewName :: String -> WithEnv String
strOrNewName "_" = newNameWith "hole"
strOrNewName s   = return s
