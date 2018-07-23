module Parse
  ( parseType
  , parseExpr
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

parseExpr :: Tree -> WithEnv Expr
parseExpr (Atom "_") = Var <$> newName
parseExpr (Atom s) = do
  msym <- definedConst s
  case msym of
    Nothing -> do
      s' <- strToName s
      return $ Var s'
    Just sym -> return $ Const sym
parseExpr (Node [Atom "thunk", te]) = do
  e <- parseExpr te
  return $ Thunk e
parseExpr (Node [Atom "lambda", Node [Atom s, tp], te]) = do
  s' <- strToName s
  p <- parseType tp
  e <- parseExpr te
  return $ Lam (S s' p) e
parseExpr (Node [Atom "return", tv]) = do
  v <- parseExpr tv
  return $ Ret v
parseExpr (Node [Atom "bind", Node [Atom s, tp], te1, te2]) = do
  s' <- strToName s
  p <- parseType tp
  e1 <- parseExpr te1
  e2 <- parseExpr te2
  return $ Bind (S s' p) e1 e2
parseExpr (Node [Atom "unthunk", tv]) = do
  v <- parseExpr tv
  return $ Unthunk v
parseExpr (Node [Atom "send", Node [Atom s, tp], te]) = do
  s' <- strToName s
  p <- parseType tp
  e <- parseExpr te
  return $ Send (S s' p) e
parseExpr (Node [Atom "receive", Node [Atom s, tp], te]) = do
  s' <- strToName s
  p <- parseType tp
  e <- parseExpr te
  return $ Recv (S s' p) e
parseExpr (Node (Atom "dispatch":te:tes))
  | not (null tes) = do
    e <- parseExpr te
    es <- mapM parseExpr tes
    return $ foldl Dispatch e es
parseExpr (Node [Atom "coleft", te]) = do
  e <- parseExpr te
  return $ Coleft e
parseExpr (Node [Atom "coright", te]) = do
  e <- parseExpr te
  return $ Coright e
parseExpr (Node [Atom "mu", Node [Atom s, tp], te]) = do
  s' <- strToName s
  p <- parseType tp
  e <- parseExpr te
  return $ Mu (S s' p) e
parseExpr (Node (Atom "case":te:tves))
  | not (null tves) = do
    e <- parseExpr te
    ves <- mapM parseClause tves
    return $ Case e ves
parseExpr (Node [Atom "ascribe", te, tn]) = do
  e <- parseExpr te
  n <- parseType tn
  return $ Asc e n
parseExpr (Node (te:tvs))
  | not (null tvs) = do
    e <- parseExpr te
    vs <- mapM parseExpr tvs
    case e of
      Const sym -> return $ foldl VApp e vs
      _         -> return $ foldl App e vs
parseExpr t = lift $ throwE $ "parseExpr: syntax error:\n" ++ Pr.ppShow t

parseClause :: Tree -> WithEnv (Expr, Expr)
parseClause (Node [tv, te]) = do
  v <- parseExpr tv
  e <- parseExpr te
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
    Just sym -> return $ TConst sym
parseType (Node [Atom "down", tn]) = do
  n <- parseType tn
  return $ TDown n
parseType (Node [Atom "constructor", Node [Atom s, tp1], tp2]) = do
  s' <- strToName s
  p1 <- parseType tp1
  p2 <- parseType tp2
  return $ TImp (S s' p1) p2
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
  modify (\e -> e {valueEnv = S x p : valueEnv e})
parseVDef t = lift $ throwE $ "parseVDef: syntax error:\n" ++ Pr.ppShow t

definedConst :: String -> WithEnv (Maybe Sym)
definedConst s = do
  env <- get
  let vEnv = valueEnv env
  return $ find (\(S x _) -> x == s) vEnv

strToName :: String -> WithEnv String
strToName "_" = newName
strToName s   = return s
