{-# LANGUAGE OverloadedStrings #-}

module Parse.Tokenize
  ( tokenize
  ) where

import Control.Monad.Except
import Control.Monad.State
import Path

import qualified Data.Set as S
import qualified Data.Text as T

import Data.Basic
import Data.Env
import Data.Log
import Data.Tree

data TEnv =
  TEnv
    { text :: T.Text
    , line :: Int
    , column :: Int
    , filePath :: Path Abs File
    }
  deriving (Show)

type Tokenizer a = StateT TEnv (ExceptT Log IO) a

tokenize :: T.Text -> WithEnv [TreePlus]
tokenize input = do
  modify (\env -> env {count = 1 + count env})
  path <- gets currentFilePath
  let env = TEnv {text = input, line = 1, column = 1, filePath = path}
  resultOrError <- liftIO $ runExceptT (runStateT program env)
  case resultOrError of
    Left err -> throwError [err]
    Right (result, _) -> return result

program :: Tokenizer [TreePlus]
program = skip >> sepEndBy term skip

term :: Tokenizer TreePlus
term = do
  s <- gets text
  case T.uncons s of
    Just ('(', _) -> node
    Just ('[', _) -> nodeSquare
    _ -> leaf

leaf :: Tokenizer TreePlus
leaf = do
  m <- currentMeta
  s <- gets text
  case T.uncons s of
    Just ('"', _) -> do
      k <- string
      skip
      return (m, TreeLeaf k)
    Just (c, _)
      | isSymbolChar c -> do
        x <- symbol
        skip
        return (m, TreeLeaf x)
      | otherwise ->
        raiseTokenizeError $
        "unexpected character: '" <>
        T.singleton c <> "'\nexpecting: SYMBOL-CHAR"
    Nothing -> raiseTokenizeError $ "unexpected end of input\nexpecting: LEAF"

node :: Tokenizer TreePlus
node = do
  m <- currentMeta
  char '(' >> skip
  itemList <- many term
  skip >> char ')' >> skip
  return (m, TreeNode itemList)

nodeSquare :: Tokenizer TreePlus
nodeSquare = do
  m <- currentMeta
  char '[' >> skip
  itemList <- many term
  skip >> char ']' >> skip
  return (m, TreeNodeSquare itemList)

char :: Char -> Tokenizer ()
char c = do
  s <- gets text
  case T.uncons s of
    Nothing ->
      raiseTokenizeError $
      "unexpected end of input\nexpecting: '" <> T.singleton c <> "'"
    Just (c', rest)
      | c == c' -> do
        if c == '\n'
          then updateStreamL rest
          else updateStreamC 1 rest
      | otherwise ->
        raiseTokenizeError $
        "unexpected character: '" <>
        T.singleton c' <> "'\nexpecting: '" <> T.singleton c <> "'"

skip :: Tokenizer ()
skip = do
  space
  s <- gets text
  case T.uncons s of
    Just (';', _) -> comment
    _ -> space

space :: Tokenizer ()
space = do
  s <- gets text
  case T.uncons s of
    Just (c, rest)
      | c `S.member` spaceSet -> updateStreamC 1 rest >> space
      | c `S.member` newlineSet -> updateStreamL rest >> space
    _ -> return ()

comment :: Tokenizer ()
comment = do
  s <- gets text
  case T.uncons s of
    Just ('\n', rest) -> updateStreamL rest >> skip
    Just (_, rest) -> updateStreamC 1 rest >> comment
    Nothing -> return () -- no newline at the end of file

many :: Tokenizer a -> Tokenizer [a]
many f = sepEndBy f (return ())

sepEndBy :: Tokenizer a -> Tokenizer () -> Tokenizer [a]
sepEndBy f g = sepEndBy' (f >>= return . Right) g []

sepEndBy' :: Tokenizer (Either [a] a) -> Tokenizer () -> [a] -> Tokenizer [a]
sepEndBy' f g acc = do
  itemOrResult <- catchError f (const $ return $ Left $ reverse acc)
  g
  case itemOrResult of
    Right item -> sepEndBy' f g (item : acc)
    Left result -> return result

symbol :: Tokenizer T.Text
symbol = do
  s <- gets text
  let x = T.takeWhile isSymbolChar s
  let rest = T.dropWhile isSymbolChar s
  updateStreamC (T.length x) rest
  return x

string :: Tokenizer T.Text
string = do
  s <- gets text
  let rest = T.tail s -- T.head s is known to be '"'
  len <- headStringLengthOf False rest 1
  let (x, rest') = T.splitAt len s
  modify (\env -> env {text = rest'})
  return x

type EscapeFlag = Bool

headStringLengthOf :: EscapeFlag -> T.Text -> Int -> Tokenizer Int
headStringLengthOf flag s i = do
  case T.uncons s of
    Nothing -> raiseTokenizeError "unexpected end of input while lexing string"
    Just (c, rest)
      | c == '"' -> do
        incrementColumn
        if flag
          then headStringLengthOf False rest (i + 1)
          else return $ i + 1
      | c == '\\' -> do
        incrementColumn
        headStringLengthOf (not flag) rest (i + 1)
      | c == '\n' -> do
        incrementLine
        headStringLengthOf False rest (i + 1)
      | otherwise -> do
        incrementColumn
        headStringLengthOf False rest (i + 1)

currentMeta :: Tokenizer Meta
currentMeta = do
  l <- gets line
  c <- gets column
  path <- gets filePath
  return $ newMeta l c path

{-# INLINE isSymbolChar #-}
isSymbolChar :: Char -> Bool
isSymbolChar c = c `S.notMember` nonSymbolSet

{-# INLINE spaceSet #-}
spaceSet :: S.Set Char
spaceSet = S.fromList " "

{-# INLINE newlineSet #-}
newlineSet :: S.Set Char
newlineSet = S.fromList "\n"

{-# INLINE nonSymbolSet #-}
nonSymbolSet :: S.Set Char
nonSymbolSet = S.fromList "()[] \"\n;"

{-# INLINE updateStreamL #-}
updateStreamL :: T.Text -> Tokenizer ()
updateStreamL s =
  modify (\env -> env {text = s, line = 1 + line env, column = 1})

{-# INLINE updateStreamC #-}
updateStreamC :: Int -> T.Text -> Tokenizer ()
updateStreamC c s = modify (\env -> env {text = s, column = c + column env})

incrementLine :: Tokenizer ()
incrementLine = modify (\env -> env {line = 1 + line env, column = 1})

incrementColumn :: Tokenizer ()
incrementColumn = modify (\env -> env {column = 1 + column env})

raiseTokenizeError :: T.Text -> Tokenizer a
raiseTokenizeError txt = do
  m <- currentMeta
  throwError $ logError (getPosInfo m) txt
