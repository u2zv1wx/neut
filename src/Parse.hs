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
parse (meta :< TreeAtom s) = do
  msym <- lookupValueEnv s
  case msym of
    Nothing -> return (meta :< TermVar s)
    Just _  -> return $ meta :< TermConst s
parse (meta :< TreeNode [_ :< TreeAtom "lambda", _ :< TreeNode ts, te]) = do
  xs <- parseArg ts
  e <- parse te
  _ :< term <- foldMTermR TermLam e xs
  return $ meta :< term
parse (meta :< TreeNode [_ :< TreeAtom "pair", t1, t2]) = do
  e1 <- parse t1
  e2 <- parse t2
  return $ meta :< TermPair e1 e2
-- parse (meta :< TreeNode [_ :< TreeAtom "destruct", _ :< TreeAtom x, _ :< TreeAtom y, t1, t2]) = do
--   e1 <- parse t1
--   e2 <- parse t2
--   return $ meta :< TermDestruct x y e1 e2
parse (meta :< TreeNode [_ :< TreeAtom "lift", tv]) = do
  v <- parse tv
  return $ meta :< TermLift v
parse (meta :< TreeNode [_ :< TreeAtom "bind", _ :< TreeAtom x, t1, t2]) = do
  e1 <- parse t1
  e2 <- parse t2
  return $ meta :< TermBind x e1 e2
parse (meta :< TreeNode [_ :< TreeAtom "thunk", te]) = do
  e <- parse te
  return $ meta :< TermThunk e
parse (meta :< TreeNode [_ :< TreeAtom "unthunk", tv]) = do
  v <- parse tv
  return $ meta :< TermUnthunk v
parse (meta :< TreeNode [_ :< TreeAtom "mu", _ :< TreeAtom x, te]) = do
  e <- parse te
  return $ meta :< TermMu x e
parse (meta :< TreeNode ((_ :< TreeAtom "match"):(_ :< TreeNode tvs):tves))
  | not (null tves) = do
    vs <- mapM parse tvs
    ves <- mapM parseClause tves
    return $ meta :< TermCase vs ves
parse (meta :< TreeNode [i :< TreeAtom x, t]) = do
  flag <- isDefinedLabel x
  e <- parse t
  if flag
    then return $ meta :< TermInject x e
    else return $ meta :< TermApp (i :< TermVar x) e
parse (meta :< TreeNode (te:tvs))
  | not (null tvs) = do
    e <- parse te
    vs <- mapM parse tvs
    _ :< tmp <- foldMTermL TermApp e vs
    return $ meta :< tmp
parse t = lift $ throwE $ "parse: syntax error:\n" ++ Pr.ppShow t

parseArg :: [Tree] -> WithEnv [Identifier]
parseArg [] = return []
parseArg (t:ts) = do
  xs <- parseArg ts
  arg <- parseArg' t
  return $ arg : xs

parseArg' :: Tree -> WithEnv Identifier
parseArg' (_ :< TreeAtom s) = return s
parseArg' t = lift $ throwE $ "parseArg': syntax error:\n" ++ Pr.ppShow t

parsePat :: Tree -> WithEnv Pat
parsePat (meta :< TreeAtom "_") = return $ meta :< PatHole
parsePat (meta :< TreeAtom s) = do
  msym <- lookupValueEnv s
  case msym of
    Nothing -> do
      s' <- strToName s
      return (meta :< PatVar s')
    Just _ -> return $ meta :< PatConst s
parsePat (meta :< TreeNode [_ :< TreeAtom "thunk", te]) = do
  e <- parsePat te
  return $ meta :< PatThunk e
parsePat (meta :< TreeNode [_ :< TreeAtom "unthunk", te]) = do
  e <- parsePat te
  return $ meta :< PatUnthunk e
parsePat (meta :< TreeNode [_ :< TreeAtom "pair", t1, t2]) = do
  p1 <- parsePat t1
  p2 <- parsePat t2
  return $ meta :< PatPair p1 p2
parsePat (meta :< TreeNode [i :< TreeAtom x, t]) = do
  undefined
  flag <- isDefinedLabel x
  e <- parsePat t
  if flag
    then return $ meta :< PatInject x e
    else return $ meta :< PatApp (i :< PatVar x) [e]
parsePat (meta :< TreeNode (t:ts)) = do
  t' <- parsePat' t
  ts' <- mapM parsePat ts
  return $ meta :< PatApp t' ts'
parsePat t = lift $ throwE $ "parsePat: syntax error:\n" ++ Pr.ppShow t

parsePat' :: Tree -> WithEnv Pat
parsePat' (meta :< TreeAtom "_") = return $ meta :< PatHole
parsePat' (meta :< TreeAtom s) = do
  msym <- lookupValueEnv s
  case msym of
    Nothing ->
      lift $ throwE $ "parsePat: the constant " ++ show s ++ " is not defined"
    Just _ -> return $ meta :< PatConst s
parsePat' (meta :< TreeNode [_ :< TreeAtom "thunk", te]) = do
  e <- parsePat' te
  return $ meta :< PatThunk e
parsePat' (meta :< TreeNode [_ :< TreeAtom "unthunk", te]) = do
  e <- parsePat' te
  return $ meta :< PatUnthunk e
parsePat' (meta :< TreeNode (t:ts)) = do
  t' <- parsePat' t
  ts' <- mapM parsePat ts
  return $ meta :< PatApp t' ts'
  -- msym <- lookupVEnv s
  -- case msym of
  --   Nothing ->
  --     lift $ throwE $ "parsePat': the constant " ++ show s ++ " is not defined"
  --   Just _ -> do
  --     ts' <- mapM parsePat' ts
  --     return $ meta :< PatApp s ts'
parsePat' t = lift $ throwE $ "parsePat': syntax error:\n" ++ Pr.ppShow t

parseClause :: Tree -> WithEnv ([Pat], Term)
parseClause (_ :< TreeNode [_ :< TreeAtom "with", _ :< TreeNode tps, tbody]) = do
  ps <- mapM parsePat tps
  body <- parse tbody
  return (ps, body)
parseClause t = lift $ throwE $ "parseClause: syntax error:\n" ++ Pr.ppShow t

parseType :: Tree -> WithEnv Type
parseType (_ :< TreeAtom "_") = do
  name <- newNameWith "hole"
  return (Fix $ TypeHole name)
parseType (_ :< TreeAtom "universe") = do
  t <- TypeUniv . WeakLevelHole <$> newName
  return $ Fix t
parseType (_ :< TreeAtom s) = do
  msym <- lookupDefinedTypeEnv s
  case msym of
    Nothing -> return (Fix $ TypeVar s)
    Just _  -> return $ Fix $ TypeNode s []
parseType (_ :< TreeNode [_ :< TreeAtom "down", tn]) = do
  n <- parseType tn
  return $ Fix $ TypeDown n
parseType (_ :< TreeNode [_ :< TreeAtom "universe", _ :< TreeAtom si]) =
  case readMaybe si of
    Nothing -> lift $ throwE $ "not a number: " ++ si
    Just j  -> return $ Fix $ TypeUniv (WeakLevelFixed j)
parseType (_ :< TreeNode [_ :< TreeAtom "forall", _ :< TreeNode ts, tn]) = do
  its <- mapM parseTypeArg ts
  n <- parseType tn
  foldMTermR' TypeForall n its
parseType (_ :< TreeNode [_ :< TreeAtom "exists", _ :< TreeNode ts, tn]) = do
  its <- mapM parseTypeArg ts
  n <- parseType tn
  foldMTermR' TypeExists n its
parseType (_ :< TreeNode ((_ :< TreeAtom "sum"):ts)) = do
  labelTypeList <- mapM parseTypeArg ts
  forM_ labelTypeList $ \(label, _) -> insLabelEnv label labelTypeList
  return $ Fix $ TypeSum labelTypeList
parseType (_ :< TreeNode [_ :< TreeAtom "up", tp]) = do
  p <- parseType tp
  return $ Fix $ TypeUp p
parseType (_ :< TreeNode ((_ :< TreeAtom s):ts)) = do
  msym <- lookupDefinedTypeEnv s
  case msym of
    Nothing -> lift $ throwE $ "the constant " ++ show s ++ " is not defined"
    Just args -- "nat" should be written as `(nat)`, for example.
      | length args == length ts -> do
        es <- mapM parseType ts
        return $ Fix $ TypeNode s es
    Just args ->
      lift $
      throwE $
      "the arity of " ++
      show s ++ " is " ++ show (length args) ++ ", not " ++ show (length ts)
parseType t = lift $ throwE $ "parseType: syntax error:\n" ++ Pr.ppShow t

parseTypeArg :: Tree -> WithEnv (Identifier, Type)
parseTypeArg (_ :< TreeNode [targ, tp]) = do
  arg <- parseArg' targ
  t <- parseType tp
  return (arg, t)
parseTypeArg t = lift $ throwE $ "parseTypeArg: syntax error:\n" ++ Pr.ppShow t

strToName :: String -> WithEnv Identifier
strToName "_" = newNameWith "hole"
strToName s   = return s
