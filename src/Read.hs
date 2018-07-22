module Read
  ( strToTree
  ) where

import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Text.Parsec                hiding (Parsec)

import           Data

type Parser a = ParsecT String () (StateT Env (ExceptT String IO)) a

strToTree :: String -> WithEnv [Tree]
strToTree input = do
  t <- runParserT (spaces >> parseSExpList) () "read" input
  case t of
    Left err -> lift $ throwE (show err)
    Right p  -> return p

parseSExpList :: Parser [Tree]
parseSExpList = sepEndBy parseStr spaces

symbol :: Parser String
symbol = many1 (noneOf "()[] \n")

parseStr :: Parser Tree
parseStr = parseNode <|> parseAtom

parseAtom :: Parser Tree
parseAtom = do
  s <- symbol
  _ <- spaces
  return $ Atom s

parseNode :: Parser Tree
parseNode = do
  _ <- char '(' >> spaces
  itemList <- many parseStr
  _ <- spaces >> char ')' >> spaces
  return $ Node itemList
