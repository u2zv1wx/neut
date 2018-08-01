module Parse
  ( parseType
  , parseTerm
  ) where

import           Control.Monad              (void)
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Data
import           Data.List
import           Data.Maybe
import           Text.Read                  (readMaybe)

import qualified Text.Show.Pretty           as Pr

parseTerm :: MTree -> WithEnv MTerm
parseTerm (Atom "_", i) = do
  name <- newNameWith "hole"
  return (Var name, i)
parseTerm (Atom s, i) = do
  msym <- definedConst s
  case msym of
    Nothing -> do
      s' <- strToName s
      return (Var s', i)
    Just (s, _) -> return (Const s, i)
parseTerm (Node [(Atom "thunk", _), te], i) = do
  e <- parseTerm te
  return (Thunk e, i)
parseTerm (Node [(Atom "lambda", _), (Node [(Atom s, _), tp], _), te], i) = do
  s' <- strToName s
  p <- parseType tp
  e <- parseTerm te
  return (Lam (s', p) e, i)
parseTerm (Node [(Atom "return", _), tv], i) = do
  v <- parseTerm tv
  return (Ret v, i)
parseTerm (Node [(Atom "bind", _), (Node [(Atom s, _), tp], _), te1, te2], i) = do
  s' <- strToName s
  p <- parseType tp
  e1 <- parseTerm te1
  e2 <- parseTerm te2
  return (Bind (s', p) e1 e2, i)
parseTerm (Node [(Atom "unthunk", _), tv], i) = do
  v <- parseTerm tv
  return (Unthunk v, i)
parseTerm (Node [(Atom "mu", _), (Node [(Atom s, _), tp], _), te], i) = do
  s' <- strToName s
  p <- parseType tp
  e <- parseTerm te
  return (Mu (s', p) e, i)
parseTerm (Node ((Atom "case", _):te:tves), i)
  | not (null tves) = do
    e <- parseTerm te
    ves <- mapM parseClause tves
    return (Case e ves, i)
parseTerm (Node [(Atom "ascribe", _), te, tn], i) = do
  e <- parseTerm te
  n <- parseType tn
  return (Asc e n, i)
parseTerm (Node (te:tvs), i)
  | not (null tvs) = do
    e <- parseTerm te
    vs <- mapM parseTerm tvs
    tmp <- foldMTerm App e vs
    return (fst tmp, i)
parseTerm t = lift $ throwE $ "parseTerm: syntax error:\n" ++ Pr.ppShow t

foldMTerm ::
     ((a, Meta) -> (a, Meta) -> a)
  -> (a, Meta)
  -> [(a, Meta)]
  -> WithEnv (a, Meta)
foldMTerm f e [] = return e
foldMTerm f e (t:ts) = do
  let tmp = f e t
  i <- newName
  foldMTerm f (tmp, Meta {ident = i}) ts

parseClause :: MTree -> WithEnv (MTerm, MTerm)
parseClause (Node [tv, te], i) = do
  v <- parseTerm tv
  e <- parseTerm te
  return (v, e)
parseClause t = lift $ throwE $ "parseClause: syntax error:\n" ++ Pr.ppShow t

parseType :: MTree -> WithEnv Type
parseType (Atom "_", i) = do
  name <- newNameWith "hole"
  return (THole name)
parseType (Atom "universe", i) = TUniv . LHole <$> newName
parseType (Atom s, i) = do
  msym <- definedConst s
  case msym of
    Nothing -> do
      s' <- strToName s
      return $ TVar s'
    Just (s, _) -> return $ TConst s
parseType (Node [(Atom "down", _), tn], i) = do
  n <- parseType tn
  return $ TDown n
parseType (Node [(Atom "universe", _), (Atom si, _)], i) =
  case readMaybe si of
    Nothing -> lift $ throwE $ "not a number: " ++ si
    Just j  -> return $ TUniv (Fixed j)
parseType (Node [(Atom "forall", _), (Node [(Atom s, _), tp], _), tn], i) = do
  s' <- strToName s
  p <- parseType tp
  n <- parseType tn
  return $ TForall (s', p) n
parseType (Node [(Atom "up", _), tp], i) = do
  p <- parseType tp
  return $ TUp p
parseType t = lift $ throwE $ "parseType: syntax error:\n" ++ Pr.ppShow t

parseVDef :: MTree -> WithEnv ()
parseVDef (Node [(Atom "value", _), (Atom x, _), tp], i) = do
  p <- parseType tp
  modify (\e -> e {valueEnv = (x, p) : valueEnv e})
parseVDef t = lift $ throwE $ "parseVDef: syntax error:\n" ++ Pr.ppShow t

definedConst :: String -> WithEnv (Maybe (String, Type))
definedConst s = do
  env <- get
  let vEnv = valueEnv env
  return $ find (\(x, _) -> x == s) vEnv

strToName :: String -> WithEnv String
strToName "_" = newNameWith "hole"
strToName s   = return s
