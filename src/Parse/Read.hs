{-# LANGUAGE OverloadedStrings #-}

module Parse.Read
  ( strToTree
  ) where

import Control.Monad.Except
import Control.Monad.State
import Text.Parsec hiding (count)

import qualified Data.IntMap.Strict as IntMap
import qualified Data.Text as T

import Data.Basic
import Data.Env
import Data.Tree

type Parser a = ParsecT T.Text () (StateT Env (ExceptT [IO ()] IO)) a

strToTree :: T.Text -> String -> WithEnv [TreePlus]
strToTree input fileName = do
  modify (\e -> e {count = 1 + count e})
  t <- runParserT (skip >> parseSExpList) () fileName input
  case t of
    Left err -> throwError' $ T.pack (show err)
    Right ts -> return ts

parseSExpList :: Parser [TreePlus]
parseSExpList = sepEndBy parseStr skip

parseStr :: Parser TreePlus
parseStr = parseNode <|> parseAtom

parseAtom :: Parser TreePlus
parseAtom = do
  m <- currentMeta
  s <- symbol
  _ <- skip
  return (m, TreeAtom s)

parseNode :: Parser TreePlus
parseNode = do
  m <- currentMeta
  _ <- char '(' >> skip
  itemList <- many parseStr
  _ <- skip >> char ')' >> skip
  return (m, TreeNode itemList)

skip :: Parser ()
skip = spaces >> (comment <|> spaces)

symbol :: Parser T.Text
symbol = do
  s <- many1 (noneOf "()[] \n;")
  return $ T.pack s

comment :: Parser ()
comment = do
  _ <- char ';'
  skipMany (noneOf "\n")
  skip

currentMeta :: Parser Meta
currentMeta = do
  pos <- getPosition
  let l = sourceLine pos
  let c = sourceColumn pos
  name <- gets currentFilePath
  return $
    Meta
      { metaFileName = Just name
      , metaLocation = Just (0, l, c)
      , metaConstraintLocation = Just (0, l, c)
      , metaIsPublic = True
      , metaIsAppropriateAsCompletionCandidate = True
      , metaUnivParams = IntMap.empty
      }
