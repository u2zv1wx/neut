module Read
  ( strToTree
  ) where

import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Text.Parsec                hiding (Parsec, count)

import           Data

type Parser a = ParsecT String () (StateT Env (ExceptT String IO)) a

strToTree :: String -> WithEnv [MTree]
strToTree input = do
  t <- runParserT (spaces >> parseSExpList) () "read" input
  case t of
    Left err -> lift $ throwE (show err)
    Right p  -> return p

parseSExpList :: Parser [MTree]
parseSExpList = sepEndBy parseStr spaces

symbol :: Parser String
symbol = many1 (noneOf "()[] \n")

parseStr :: Parser MTree
parseStr = parseNode <|> parseAtom

parseAtom :: Parser MTree
parseAtom = do
  s <- symbol
  _ <- spaces
  i <- newNameParser
  return (Atom s, Meta {ident = i, regionSet = []})

parseNode :: Parser MTree
parseNode = do
  _ <- char '(' >> spaces
  itemList <- many parseStr
  _ <- spaces >> char ')' >> spaces
  i <- newNameParser
  return (Node itemList, Meta {ident = i, regionSet = []})

newNameParser :: Parser String
newNameParser = do
  env <- get
  let i = count env
  modify (\e -> e {count = i + 1})
  return $ "#" ++ show i
