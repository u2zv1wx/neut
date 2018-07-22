module Parse
  ( parse
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

parse :: Tree -> WithEnv Term
parse = tryOptions [fmap ValueDefinition . parseVDef, fmap Expr . parseE]

parseE :: Tree -> WithEnv E
parseE (Atom s) = do
  s' <- strToName s
  return $ Var s'
parseE (Node [Atom "thunk", te]) = do
  e <- parseE te
  return $ Thunk e
parseE (Node [Atom "lambda", Node [Atom s, tp], te]) = do
  s' <- strToName s
  p <- parseType tp
  e <- parseE te
  return $ Lam (S s' p) e
parseE (Node [Atom "return", tv]) = do
  v <- parseE tv
  return $ Ret v
parseE (Node [Atom "bind", Node [Atom s, tp], te1, te2]) = do
  s' <- strToName s
  p <- parseType tp
  e1 <- parseE te1
  e2 <- parseE te2
  return $ Bind (S s' p) e1 e2
parseE (Node [Atom "unthunk", tv]) = do
  v <- parseE tv
  return $ Unthunk v
parseE (Node [Atom "send", Node [Atom s, tp], te]) = do
  s' <- strToName s
  p <- parseType tp
  e <- parseE te
  return $ Send (S s' p) e
parseE (Node [Atom "receive", Node [Atom s, tp], te]) = do
  s' <- strToName s
  p <- parseType tp
  e <- parseE te
  return $ Receive (S s' p) e
parseE (Node (Atom "dispatch":tes))
  | length tes >= 2 = do
    es <- mapM parseE tes
    return $ Dispatch es
parseE (Node [Atom "select", Atom si, te]) =
  case readMaybe si of
    Nothing -> lift $ throwE $ "not a number: " ++ si
    Just i -> do
      e <- parseE te
      return $ Select i e
parseE (Node [Atom "mu", Node [Atom s, tp], te]) = do
  s' <- strToName s
  p <- parseType tp
  e <- parseE te
  return $ Mu (S s' p) e
parseE (Node (Atom "case":te:tves))
  | not (null tves) = do
    e <- parseE te
    ves <- mapM parseClause tves
    return $ Case e ves
parseE (Node [Atom "ascribe", te, tn]) = do
  e <- parseE te
  n <- parseType tn
  return $ Asc e n
parseE (Node (te:tvs))
  | not (null tvs) = do
    e <- parseE te
    vs <- mapM parseE tvs
    return $ foldl App e vs
parseE t = lift $ throwE $ "parseE: syntax error:\n" ++ Pr.ppShow t

parseClause :: Tree -> WithEnv (E, E)
parseClause (Node [tv, te]) = do
  v <- parseE tv
  e <- parseE te
  return (v, e)
parseClause t = lift $ throwE $ "parseClause: syntax error:\n" ++ Pr.ppShow t

parseType :: Tree -> WithEnv T
parseType (Atom "_") = THole <$> newName
parseType (Atom s) = do
  s' <- strToName s
  return $ PVar s'
parseType (Node [Atom "down", tn]) = do
  n <- parseType tn
  return $ Down n
parseType (Node [Atom "constructor", Node [Atom s, tp1], tp2]) = do
  s' <- strToName s
  p1 <- parseType tp1
  p2 <- parseType tp2
  return $ PImp (S s' p1) p2
parseType (Node [Atom "universe", Atom si]) =
  case readMaybe si of
    Nothing -> lift $ throwE $ "not a number: " ++ si
    Just i  -> return $ Universe i
parseType (Node [Atom "forall", Node [Atom s, tp], tn]) = do
  s' <- strToName s
  p <- parseType tp
  n <- parseType tn
  return $ Forall (S s' p) n
parseType (Node (Atom "par":tns))
  | length tns >= 2 = do
    ns <- mapM parseType tns
    return $ Par ns
parseType (Node [Atom "up", tp]) = do
  p <- parseType tp
  return $ Up p
parseType t = lift $ throwE $ "syntax error:\n" ++ Pr.ppShow t

parseVDef :: Tree -> WithEnv VDef
parseVDef (Node [Atom "value", Atom x, tp]) = do
  p <- parseType tp
  return $ VDef {consName = S x p}
parseVDef t = lift $ throwE $ "syntax error:\n" ++ Pr.ppShow t

strToName :: String -> WithEnv String
strToName "_" = newName
strToName s   = return s
