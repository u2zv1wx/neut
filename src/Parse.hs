module Parse
  ( parseType
  , parseComp
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
import           Pattern
import           Text.Read                  (readMaybe)

import qualified Text.Show.Pretty           as Pr

parseValue :: Tree -> WithEnv QuasiValue
parseValue (meta :< TreeAtom "_") = do
  name <- newNameWith "hole"
  return $ QuasiValue $ meta :< ValueVar name
parseValue (meta :< TreeAtom s) = return $ QuasiValue (meta :< ValueVar s)
parseValue (meta :< TreeNode [_ :< TreeAtom "thunk", te]) = do
  e <- parseComp te
  return $ QuasiValue (meta :< ValueThunk e)
parseValue (meta :< TreeNode ((_ :< TreeAtom s):ts)) = do
  msym <- lookupVEnv s
  case msym of
    Nothing -> lift $ throwE "(polarity)"
    Just (s, args, _) -- "zero" should be written as `(zero)`, for example.
      | length args == length ts -> do
        vs <- mapM parseValue ts
        let vs' = map (\(QuasiValue v) -> v) vs
        return $ QuasiValue $ meta :< ValueNodeApp s vs'
    Just (s, args, _) -> do
      lift $
        throwE $
        "the arity of " ++
        show s ++ " is " ++ show (length args) ++ ", not " ++ show (length ts)
parseValue t = lift $ throwE $ "parseValue: syntax error:\n" ++ Pr.ppShow t

parseComp :: Tree -> WithEnv QuasiComp
parseComp (meta :< TreeNode [_ :< TreeAtom "lambda", _ :< TreeNode ts, te]) = do
  xs <- parseIdentSeq ts
  QuasiComp e <- parseComp te
  _ :< term <- foldMTermR QuasiCompLam e xs
  return $ QuasiComp $ meta :< term
parseComp (meta :< TreeNode [_ :< TreeAtom "return", tv]) = do
  v <- parseValue tv
  return $ QuasiComp $ meta :< QuasiCompRet v
parseComp (meta :< TreeNode [_ :< TreeAtom "bind", _ :< TreeAtom s, te1, te2]) = do
  s' <- strOrNewName s
  QuasiComp e1 <- parseComp te1
  QuasiComp e2 <- parseComp te2
  return $ QuasiComp $ meta :< QuasiCompBind s' e1 e2
parseComp (meta :< TreeNode [_ :< TreeAtom "unthunk", tv]) = do
  v <- parseValue tv
  return $ QuasiComp $ meta :< QuasiCompUnthunk v
parseComp (meta :< TreeNode [_ :< TreeAtom "mu", _ :< TreeAtom s, te]) = do
  s' <- strOrNewName s
  QuasiComp e <- parseComp te
  return $ QuasiComp $ meta :< QuasiCompMu s' e
parseComp (meta :< TreeNode ((_ :< TreeAtom "match"):(_ :< TreeNode tvs):tves))
  | not (null tves) = do
    vs <- mapM parseValue tvs
    ves <- mapM parseClause tves
    return $ QuasiComp $ meta :< QuasiCompCase vs ves
parseComp (_ :< TreeNode (te@(_ :< TreeAtom s):ts)) = do
  msym <- lookupVEnv s
  case msym of
    Nothing -> parseCompApp te ts
    Just _ -> do
      lift $ throwE "parseComp.compapp"
parseComp (_ :< TreeNode (te:tvs))
  | not (null tvs) = parseCompApp te tvs
parseComp t = lift $ throwE $ "parseComp: syntax error:\n" ++ Pr.ppShow t

parseCompApp :: Tree -> [Tree] -> WithEnv QuasiComp
parseCompApp te tvs = do
  QuasiComp e <- parseComp te
  vs <- mapM parseValue tvs
  QuasiComp <$> foldMTerm QuasiCompApp e vs

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

parseClause :: Tree -> WithEnv ([Pat], PreQuasiComp)
parseClause (_ :< TreeNode [(_ :< TreeAtom "with"), (_ :< TreeNode tps), tbody]) = do
  ps <- mapM parsePat tps
  QuasiComp body <- parseComp tbody
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
