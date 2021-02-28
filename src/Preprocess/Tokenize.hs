module Preprocess.Tokenize
  ( tokenize,
  )
where

import Control.Exception.Safe
import Control.Monad.State.Lazy
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Hint
import Data.Log
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Tree
import Path

data TEnv = TEnv
  { tPhase :: Int,
    text :: T.Text,
    line :: Int,
    column :: Int,
    filePath :: Path Abs File
  }
  deriving (Show)

type Tokenizer a = StateT TEnv IO a

tokenize :: T.Text -> WithEnv [TreePlus]
tokenize input = do
  modify (\env -> env {count = 1 + count env})
  path <- getCurrentFilePath
  ph <- gets phase
  let env = TEnv {tPhase = ph, text = input, line = 1, column = 1, filePath = path}
  resultOrError <- liftIO $ try $ runStateT (program []) env
  case resultOrError of
    Left err ->
      throw (err :: Error)
    Right (result, _) ->
      return result

program :: [TreePlus] -> Tokenizer [TreePlus]
program acc = do
  skip
  s <- gets text
  if T.null s
    then return $ reverse acc
    else do
      t <- term
      program $ t : acc

term :: Tokenizer TreePlus
term = do
  s <- gets text
  case T.uncons s of
    Just (c, _)
      | Just l <- Map.lookup c readMacroMap ->
        resolveReadMacro c l
    Just ('(', _) ->
      node
    _ ->
      leaf

leaf :: Tokenizer TreePlus
leaf = do
  m <- currentHint
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
          "unexpected character: '"
            <> T.singleton c
            <> "'\nexpecting: SYMBOL-CHAR"
    Nothing ->
      raiseTokenizeError "unexpected end of input\nexpecting: LEAF"

node :: Tokenizer TreePlus
node = do
  m <- currentHint
  char '(' >> skip
  itemList <- many term
  skip >> char ')' >> skip
  return (m, TreeNode itemList)

resolveReadMacro :: Char -> T.Text -> Tokenizer TreePlus
resolveReadMacro from to = do
  m <- currentHint
  char from >> skip
  item <- term
  skip
  return (m, TreeNode [(m, TreeLeaf to), item])

char :: Char -> Tokenizer ()
char c = do
  s <- gets text
  case T.uncons s of
    Nothing ->
      raiseTokenizeError $
        "unexpected end of input\nexpecting: '" <> T.singleton c <> "'"
    Just (c', rest)
      | c == c' ->
        if c `S.member` newlineSet
          then updateStreamL rest
          else updateStreamC 1 rest
      | otherwise ->
        raiseTokenizeError $
          "unexpected character: '"
            <> T.singleton c'
            <> "'\nexpecting: '"
            <> T.singleton c
            <> "'"

skip :: Tokenizer ()
skip = do
  s <- gets text
  case T.uncons s of
    Just (c, rest)
      | c == ';' ->
        comment
      | c `S.member` newlineSet ->
        updateStreamL rest >> skip
      | c `S.member` spaceSet ->
        updateStreamC 1 rest >> skip
    _ ->
      return ()

comment :: Tokenizer ()
comment = do
  s <- gets text
  case T.uncons s of
    Just (c, rest)
      | c `S.member` newlineSet ->
        updateStreamL rest >> skip
      | otherwise ->
        updateStreamC 1 rest >> comment
    Nothing ->
      return ()

many :: Tokenizer a -> Tokenizer [a]
many f =
  sepEndBy f (return ())

sepEndBy :: Tokenizer a -> Tokenizer () -> Tokenizer [a]
sepEndBy f g =
  sepEndBy' (f >>= return . Right) g []

sepEndBy' :: Tokenizer (Either [a] a) -> Tokenizer () -> [a] -> Tokenizer [a]
sepEndBy' f g acc = do
  itemOrResult <- catch f (finalize acc)
  g
  case itemOrResult of
    Right item ->
      sepEndBy' f g (item : acc)
    Left result ->
      return result

finalize :: [a] -> Error -> Tokenizer (Either [a] a)
finalize acc _ =
  return $ Left $ reverse acc

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

type EscapeFlag =
  Bool

headStringLengthOf :: EscapeFlag -> T.Text -> Int -> Tokenizer Int
headStringLengthOf flag s i =
  case T.uncons s of
    Nothing ->
      raiseTokenizeError "unexpected end of input while lexing string"
    Just (c, rest)
      | c == '"' -> do
        incrementColumn
        if flag
          then headStringLengthOf False rest (i + 1)
          else return $ i + 1
      | c == '\\' -> do
        incrementColumn
        headStringLengthOf (not flag) rest (i + 1)
      | c `S.member` newlineSet -> do
        incrementLine
        headStringLengthOf False rest (i + 1)
      | otherwise -> do
        incrementColumn
        headStringLengthOf False rest (i + 1)

currentHint :: Tokenizer Hint
currentHint = do
  ph <- gets tPhase
  l <- gets line
  c <- gets column
  path <- gets filePath
  return $ newHint ph (fromEnum l) (fromEnum c) path

{-# INLINE isSymbolChar #-}
isSymbolChar :: Char -> Bool
isSymbolChar c =
  c `S.notMember` nonSymbolSet

{-# INLINE spaceSet #-}
spaceSet :: S.Set Char
spaceSet =
  S.fromList " "

{-# INLINE newlineSet #-}
newlineSet :: S.Set Char
newlineSet =
  S.fromList "\n"

{-# INLINE nonSymbolSet #-}
nonSymbolSet :: S.Set Char
nonSymbolSet =
  S.fromList "() \"\n;`#"

{-# INLINE updateStreamL #-}
updateStreamL :: T.Text -> Tokenizer ()
updateStreamL s =
  modify (\env -> env {text = s, line = 1 + line env, column = 1})

{-# INLINE updateStreamC #-}
updateStreamC :: Int -> T.Text -> Tokenizer ()
updateStreamC c s =
  modify (\env -> env {text = s, column = c + column env})

incrementLine :: Tokenizer ()
incrementLine =
  modify (\env -> env {line = 1 + line env, column = 1})

incrementColumn :: Tokenizer ()
incrementColumn =
  modify (\env -> env {column = 1 + column env})

raiseTokenizeError :: T.Text -> Tokenizer a
raiseTokenizeError txt = do
  m <- currentHint
  throw $ Error [logError (getPosInfo m) txt]

-- '*' を "raw-pointer" にしてもいいかも。
readMacroMap :: Map.HashMap Char T.Text
readMacroMap =
  Map.fromList
    [ -- ('\'', "quote"),
      -- (',', "unquote"),
      ('`', "quasiquote"),
      ('#', "quasiunquote")
    ]
