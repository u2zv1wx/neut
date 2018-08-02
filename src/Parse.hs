module Parse
  ( parseType
  , parseTerm
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
parseTerm (meta :< TreeAtom s) = do
  msym <- definedConst s
  case msym of
    Nothing -> do
      s' <- strToName s
      return (meta :< WeakTermVar s')
    Just (s, _) -> return (meta :< WeakTermConst s)
parseTerm (meta :< TreeNode [_ :< TreeAtom "thunk", te]) = do
  e <- parseTerm te
  return (meta :< WeakTermThunk e)
parseTerm (meta :< TreeNode [_ :< TreeAtom "lambda", _ :< TreeNode [_ :< TreeAtom s, tp], te]) = do
  s' <- strToName s
  p <- parseType tp
  e <- parseTerm te
  return (meta :< WeakTermLam (s', p) e)
parseTerm (meta :< TreeNode [_ :< TreeAtom "return", tv]) = do
  v <- parseTerm tv
  return (meta :< WeakTermRet v)
parseTerm (meta :< TreeNode [_ :< TreeAtom "bind", _ :< TreeNode [_ :< TreeAtom s, tp], te1, te2]) = do
  s' <- strToName s
  p <- parseType tp
  e1 <- parseTerm te1
  e2 <- parseTerm te2
  return (meta :< WeakTermBind (s', p) e1 e2)
parseTerm (meta :< TreeNode [_ :< TreeAtom "unthunk", tv]) = do
  v <- parseTerm tv
  return (meta :< WeakTermUnthunk v)
parseTerm (meta :< TreeNode [_ :< TreeAtom "mu", _ :< TreeNode [_ :< TreeAtom s, tp], te]) = do
  s' <- strToName s
  p <- parseType tp
  e <- parseTerm te
  return (meta :< WeakTermMu (s', p) e)
parseTerm (meta :< TreeNode ((_ :< TreeAtom "case"):te:tves))
  | not (null tves) = do
    e <- parseTerm te
    ves <- mapM parseClause tves
    return (meta :< WeakTermCase e ves)
parseTerm (meta :< TreeNode [_ :< TreeAtom "ascribe", te, tn]) = do
  e <- parseTerm te
  n <- parseType tn
  return (meta :< WeakTermAsc e n)
parseTerm (meta :< TreeNode (te@(_ :< TreeAtom s):ts)) = do
  msym <- definedConst s
  case msym of
    Nothing -> parseTermApp te ts
    Just _  -> parseTermNodeApp te ts
parseTerm (_ :< TreeNode (te:tvs))
  | not (null tvs) = parseTermApp te tvs
parseTerm t = lift $ throwE $ "parseTerm: syntax error:\n" ++ Pr.ppShow t

parseTermApp :: Tree -> [Tree] -> WithEnv WeakTerm
parseTermApp te tvs = do
  e <- parseTerm te
  vs <- mapM parseTerm tvs
  foldMTerm WeakTermApp e vs

parseTermNodeApp :: Tree -> [Tree] -> WithEnv WeakTerm
parseTermNodeApp te tvs = do
  e <- parseTerm te
  vs <- mapM parseTerm tvs
  foldMTerm WeakTermNodeApp e vs

foldMTerm ::
     (Cofree f Meta -> a -> f (Cofree f Meta))
  -> Cofree f Meta
  -> [a]
  -> StateT Env (ExceptT String IO) (Cofree f Meta)
foldMTerm f e [] = return e
foldMTerm f e (t:ts) = do
  let tmp = f e t
  i <- newName
  foldMTerm f (Meta {ident = i} :< tmp) ts

parsePat :: Tree -> WithEnv Pat
parsePat (meta :< TreeAtom s) = do
  msym <- definedConst s
  case msym of
    Nothing -> do
      s' <- strToName s
      return (meta :< PatVar s')
    Just (s, _) -> return (meta :< PatConst s)
parsePat (meta :< TreeNode (te@(_ :< TreeAtom s):ts)) = do
  te' <- parsePat te
  ts' <- mapM parsePat ts
  foldMTerm PatApp te' ts'
parsePat t = lift $ throwE $ "parsePat: syntax error:\n" ++ Pr.ppShow t

parseClause :: Tree -> WithEnv (Pat, WeakTerm)
parseClause (meta :< TreeNode [tv, te]) = do
  v <- parsePat tv
  e <- parseTerm te
  return (v, e)
parseClause t = lift $ throwE $ "parseClause: syntax error:\n" ++ Pr.ppShow t

parseType :: Tree -> WithEnv WeakType
parseType (meta :< TreeAtom "_") = do
  name <- newNameWith "hole"
  return (WeakTypeHole name)
parseType (meta :< TreeAtom "universe") =
  WeakTypeUniv . WeakLevelHole <$> newName
parseType (meta :< TreeAtom s) = do
  msym <- definedConst s
  case msym of
    Nothing -> do
      s' <- strToName s
      return $ WeakTypeVar s'
    Just (s, _) -> return $ WeakTypeConst s
parseType (meta :< TreeNode [_ :< TreeAtom "down", tn]) = do
  n <- parseType tn
  return $ WeakTypeDown n
parseType (meta :< TreeNode [_ :< TreeAtom "universe", _ :< TreeAtom si]) =
  case readMaybe si of
    Nothing -> lift $ throwE $ "not a number: " ++ si
    Just j  -> return $ WeakTypeUniv (WeakLevelFixed j)
parseType (meta :< TreeNode [_ :< TreeAtom "forall", _ :< TreeNode [_ :< TreeAtom s, tp], tn]) = do
  s' <- strToName s
  p <- parseType tp
  n <- parseType tn
  return $ WeakTypeForall (s', p) n
parseType (meta :< TreeNode [_ :< TreeAtom "node", _ :< TreeNode [_ :< TreeAtom s, tp], tn]) = do
  s' <- strToName s
  p <- parseType tp
  n <- parseType tn
  return $ WeakTypeNode (s', p) n
parseType (meta :< TreeNode [_ :< TreeAtom "up", tp]) = do
  p <- parseType tp
  return $ WeakTypeUp p
parseType t = lift $ throwE $ "parseType: syntax error:\n" ++ Pr.ppShow t

definedConst :: String -> WithEnv (Maybe (String, ValueType))
definedConst s = do
  env <- get
  let vEnv = valueEnv env
  return $ find (\(x, _) -> x == s) vEnv

strToName :: String -> WithEnv String
strToName "_" = newNameWith "hole"
strToName s   = return s
