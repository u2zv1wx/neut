module Parse.Read
  ( strToTree
  ) where

import Control.Monad.Except
import Control.Monad.State
import Text.Parsec

import Data.Basic
import Data.Env
import Data.Tree

type Parser a = ParsecT String () (StateT Env (ExceptT String IO)) a

strToTree :: String -> WithEnv [TreePlus]
strToTree input = do
  t <- runParserT (skip >> parseSExpList) () "read" input
  case t of
    Left err -> throwError (show err)
    Right p -> return p

parseSExpList :: Parser [TreePlus]
parseSExpList = sepEndBy parseStr skip

symbol :: Parser String
symbol = many1 (noneOf "()[] \n;")

parseStr :: Parser TreePlus
parseStr = parseNode <|> parseAtom

parseAtom :: Parser TreePlus
parseAtom = do
  s <- symbol
  _ <- skip
  return (emptyMeta, TreeAtom s)

parseNode :: Parser TreePlus
parseNode = do
  _ <- char '(' >> skip
  itemList <- many parseStr
  _ <- skip >> char ')' >> skip
  return (emptyMeta, TreeNode itemList)

skip :: Parser ()
skip = spaces >> (comment <|> spaces)

comment :: Parser ()
comment = do
  _ <- char ';'
  skipMany (noneOf "\n")
  skip
