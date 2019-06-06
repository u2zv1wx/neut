module Parse.Read
  ( strToTree
  ) where

import           Control.Comonad.Cofree
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Text.Parsec                hiding (count)

import           Data.Env
import           Data.Tree

type Parser a = ParsecT String () (StateT Env (ExceptT String IO)) a

strToTree :: String -> WithEnv [Tree]
strToTree input = do
  t <- runParserT (skip >> parseSExpList) () "read" input
  case t of
    Left err -> lift $ throwE (show err)
    Right p  -> return p

parseSExpList :: Parser [Tree]
parseSExpList = sepEndBy parseStr skip

symbol :: Parser String
symbol = many1 (noneOf "()[] \n;")

parseStr :: Parser Tree
parseStr = parseNode <|> parseAtom

parseAtom :: Parser Tree
parseAtom = do
  s <- symbol
  _ <- skip
  i <- newNameParser
  return $ i :< TreeAtom s

parseNode :: Parser Tree
parseNode = do
  _ <- char '(' >> skip
  itemList <- many parseStr
  _ <- skip >> char ')' >> skip
  i <- newNameParser
  return $ i :< TreeNode itemList

newNameParser :: Parser String
newNameParser = do
  env <- get
  let i = count env
  modify (\e -> e {count = i + 1})
  return $ "meta." ++ show i

skip :: Parser ()
skip = spaces >> (comment <|> spaces)

comment :: Parser ()
comment = do
  _ <- char ';'
  skipMany (noneOf "\n")
  skip
