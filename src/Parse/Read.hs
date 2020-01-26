{-# LANGUAGE OverloadedStrings #-}

module Parse.Read
  ( strToTree
  ) where

import Control.Monad.Except
import Control.Monad.State
import Text.Parsec hiding (count)

-- import Text.Parsec.Text
import qualified Data.Text as T

import Data.Basic
import Data.Env
import Data.Tree

type Parser a = ParsecT T.Text () (StateT Env (ExceptT [IO ()] IO)) a

-- type Parser a = ParsecT T.Text () (StateT Env (ExceptT T.Text IO)) a
-- {} strToTree {}
-- (as long as the input is translated into a tree, this function is considered valid)
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

symbol :: Parser Identifier
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
  let l = toInteger $ sourceLine pos
  let c = toInteger $ sourceColumn pos
  name <- gets currentFilePath
  i <- gets count -- fixme: phaseごとにiがちゃんと増加するように修正すること
  -- いちおうこれでもいいけどさ。パフォーマンス的にどうなんだろう？対して問題ないかな。
  -- いや、これでも、特定のファイルを読んだあとで別なファイルを読んだら、その別なファイルのほうがつねに値が大きくなってしまう。
  -- やっぱファイル読み込みの順番を保持する必要がある。
  -- というかincludeGraphを使えばいいんでは。DFSしたらリストになるし。それでいいね。はい。
  -- modify (\env -> env {count = 1 + count env})
  -- i <- newCount
  return $
    Meta
      { metaFileName = Just name
      , metaLocation = Just (i, l, c)
      , metaConstraintLocation = Just (i, l, c)
      }
