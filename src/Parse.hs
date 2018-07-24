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

parseTerm :: Tree -> WithEnv Term
parseTerm (Atom "_") = Var <$> newName
parseTerm (Atom s) = do
  msym <- definedConst s
  case msym of
    Nothing -> do
      s' <- strToName s
      return $ Var s'
    Just (s, _) -> return $ Const s
parseTerm (Node [Atom "thunk", te]) = do
  e <- parseTerm te
  return $ Thunk e
parseTerm (Node [Atom "lambda", Node [Atom s, tp], te]) = do
  s' <- strToName s
  p <- parseType tp
  e <- parseTerm te
  return $ Lam (S s' p) e
parseTerm (Node [Atom "return", tv]) = do
  v <- parseTerm tv
  return $ Ret v
parseTerm (Node [Atom "bind", Node [Atom s, tp], te1, te2]) = do
  s' <- strToName s
  p <- parseType tp
  e1 <- parseTerm te1
  e2 <- parseTerm te2
  return $ Bind (S s' p) e1 e2
parseTerm (Node [Atom "unthunk", tv]) = do
  v <- parseTerm tv
  return $ Unthunk v
parseTerm (Node [Atom "send", Node [Atom s, tp], te]) = do
  s' <- strToName s
  p <- parseType tp
  e <- parseTerm te
  return $ Send (S s' p) e
parseTerm (Node [Atom "receive", Node [Atom s, tp], te]) = do
  s' <- strToName s
  p <- parseType tp
  e <- parseTerm te
  return $ Recv (S s' p) e
parseTerm (Node (Atom "dispatch":te:tes))
  | not (null tes) = do
    e <- parseTerm te
    es <- mapM parseTerm tes
    return $ foldl Dispatch e es
parseTerm (Node [Atom "coleft", te]) = do
  e <- parseTerm te
  return $ Coleft e
parseTerm (Node [Atom "coright", te]) = do
  e <- parseTerm te
  return $ Coright e
parseTerm (Node [Atom "mu", Node [Atom s, tp], te]) = do
  s' <- strToName s
  p <- parseType tp
  e <- parseTerm te
  return $ Mu (S s' p) e
parseTerm (Node (Atom "case":te:tves))
  | not (null tves) = do
    e <- parseTerm te
    ves <- mapM parseClause tves
    return $ Case e ves
parseTerm (Node [Atom "ascribe", te, tn]) = do
  e <- parseTerm te
  n <- parseType tn
  return $ Asc e n
parseTerm (Node (te:tvs))
  | not (null tvs) = do
    e <- parseTerm te
    vs <- mapM parseTerm tvs
    case e of
      Const sym -> return $ foldl ConsApp e vs
      _         -> return $ foldl App e vs
parseTerm t = lift $ throwE $ "parseTerm: syntax error:\n" ++ Pr.ppShow t

parseClause :: Tree -> WithEnv (Term, Term)
parseClause (Node [tv, te]) = do
  v <- parseTerm tv
  e <- parseTerm te
  return (v, e)
parseClause t = lift $ throwE $ "parseClause: syntax error:\n" ++ Pr.ppShow t

parseType :: Tree -> WithEnv Type
parseType (Atom "_") = THole <$> newName
parseType (Atom "universe") = TUniv . LHole <$> newName
parseType (Atom s) = do
  msym <- definedConst s
  case msym of
    Nothing -> do
      s' <- strToName s
      return $ TVar s'
    Just (s, _) -> return $ TConst s
parseType (Node [Atom "down", tn]) = do
  n <- parseType tn
  return $ TDown n
parseType (Node [Atom "node", Node [Atom s, tp1], tp2]) = do
  s' <- strToName s
  p1 <- parseType tp1
  p2 <- parseType tp2
  return $ TNode (S s' p1) p2
parseType (Node [Atom "universe", Atom si]) =
  case readMaybe si of
    Nothing -> lift $ throwE $ "not a number: " ++ si
    Just i  -> return $ TUniv (Fixed i)
parseType (Node [Atom "forall", Node [Atom s, tp], tn]) = do
  s' <- strToName s
  p <- parseType tp
  n <- parseType tn
  return $ TForall (S s' p) n
parseType (Node (Atom "par":tn:tns))
  | not (null tns) = do
    n <- parseType tn
    ns <- mapM parseType tns
    return $ foldl TCotensor n ns
parseType (Node [Atom "up", tp]) = do
  p <- parseType tp
  return $ TUp p
parseType t = lift $ throwE $ "parseType: syntax error:\n" ++ Pr.ppShow t

parseVDef :: Tree -> WithEnv ()
parseVDef (Node [Atom "value", Atom x, tp]) = do
  p <- parseType tp
  modify (\e -> e {valueEnv = (x, p) : valueEnv e})
parseVDef t = lift $ throwE $ "parseVDef: syntax error:\n" ++ Pr.ppShow t

definedConst :: String -> WithEnv (Maybe (String, Type))
definedConst s = do
  env <- get
  let vEnv = valueEnv env
  return $ find (\(x, _) -> x == s) vEnv

strToName :: String -> WithEnv String
strToName "_" = newName
strToName s   = return s
