module Preprocess.Parse
  ( parse,
  )
where

import Control.Exception.Safe
import Data.Basic
import Data.Global
import Data.IORef
import Data.Log
import qualified Data.Set as S
import qualified Data.Text as T
import Data.PreTerm
import System.IO.Unsafe (unsafePerformIO)

type EscapeFlag =
  Bool

{-# NOINLINE text #-}
text :: IORef T.Text
text =
  unsafePerformIO (newIORef "")

{-# NOINLINE line #-}
line :: IORef Int
line =
  unsafePerformIO (newIORef 1)

{-# NOINLINE column #-}
column :: IORef Int
column =
  unsafePerformIO (newIORef 1)

parse :: T.Text -> IO PreTermPlus
parse input = do
  modifyIORef' text $ \_ -> input
  skip
  term

term :: IO PreTermPlus
term = do
  termPi <|> termPiIntro <|> termEnumElim <|> termQuestion <|> termCase <|> termCaseNoetic <|> termCocase <|> termLet <|> termLetCoproduct <|> termPiElim <|> termString <|> termSymbol

termSymbol :: IO PreTermPlus
termSymbol = do
  m <- currentHint
  x <- symbol
  skip
  if isKeyword x
    then raiseParseError "found a keyword, expecting a symbol"
    else return (m, PreTermSymbol x)

termPi :: IO PreTermPlus
termPi = do
  m <- currentHint
  token "pi"
  skip
  varList <- many ascription
  skip
  char '.'
  skip
  e <- term
  skip
  return (m, PreTermPi varList e)

termPiIntro ::  IO PreTermPlus
termPiIntro = do
  m <- currentHint
  token "lambda"
  skip
  varList <- many ascription
  skip
  char '.'
  skip
  e <- term
  skip
  return (m, PreTermPiIntro varList e)

termPiElim :: IO PreTermPlus
termPiElim = do
  m <- currentHint
  e1 <- termSimple
  skip
  e2 <- termSimple
  skip
  es <- sepEndBy termSimple skip
  skip
  return (m, PreTermPiElim e1 (e2 : es))

termSimple :: IO PreTermPlus
termSimple =
  termString <|> termSymbol <|> termParen

termString :: IO PreTermPlus
termString = do
  m <- currentHint
  char '"'
  s <- string
  return (m, PreTermString s)

termParen :: IO PreTermPlus
termParen = do
  char '('
  skip
  e <- term
  skip
  char ')'
  skip
  return e

termEnumElim :: IO PreTermPlus
termEnumElim = do
  m <- currentHint
  token "switch"
  skip
  e <- term
  token "with"
  skip
  clauseList <- many enumClause
  skip
  return (m, PreTermEnumElim e clauseList)

enumClause :: IO (T.Text, PreTermPlus)
enumClause = do
  token "-"
  skip
  c <- symbol
  skip
  token "->"
  skip
  body <- term
  skip
  return (c, body)

termQuestion :: IO PreTermPlus
termQuestion = do
  m <- currentHint
  token "question"
  skip
  e <- term
  skip
  return (m, PreTermQuestion e)

termCase :: IO PreTermPlus
termCase = do
  m <- currentHint
  token "match"
  skip
  e <- term
  token "with"
  skip
  clauseList <- many caseClause
  skip
  return (m, PreTermCase False e clauseList)



termCaseNoetic :: IO PreTermPlus
termCaseNoetic = do
  m <- currentHint
  token "match-noetic"
  skip
  e <- term
  token "with"
  skip
  clauseList <- many caseClause
  skip
  return (m, PreTermCase True e clauseList)


caseClause :: IO (PrePattern, PreTermPlus)
caseClause = do
  token "-"
  skip
  pa <- pat
  skip
  body <- term
  skip
  return (pa, body)

pat :: IO PrePattern
pat = do
  m <- currentHint
  c <- symbol
  skip
  argList <- patArg
  skip
  return (m, c, argList)

patArg :: IO [T.Text]
patArg = do
  x <- symbol
  skip
  if x == "->"
    then return []
    else do
      tmp <- patArg
      skip
      return $ x : tmp

termCocase :: IO PreTermPlus
termCocase = do
  m <- currentHint
  token "new"
  skip
  x <- symbol
  skip
  token "with"
  skip
  clauseList <- many cocaseClause
  skip
  return (m, PreTermCocase x clauseList)

cocaseClause :: IO (T.Text, PreTermPlus)
cocaseClause = do
  token "-"
  skip
  c <- symbol
  skip
  token "<-"
  skip
  body <- term
  skip
  return (c, body)

-- (x : A)
ascription :: IO PreIdentPlus
ascription = do
  m <- currentHint
  char '('
  skip
  x <- symbol
  skip
  char ':'
  skip
  a <- term
  skip
  char ')'
  skip
  return (m, x, a)

termLet :: IO PreTermPlus
termLet = do
  m <- currentHint
  token "let"
  skip
  x <- symbol
  skip
  char '='
  skip
  e1 <- term
  skip
  token "in"
  skip
  e2 <- term
  return (m, PreTermLet x e1 e2)

termLetCoproduct :: IO PreTermPlus
termLetCoproduct = do
  m <- currentHint
  token "let?"
  skip
  x <- symbol
  skip
  char '='
  skip
  e1 <- term
  skip
  token "in"
  skip
  e2 <- term
  return (m, PreTermLetCoproduct x e1 e2)


token :: T.Text -> IO ()
token s = do
  x <- symbol
  if x == s
    then return ()
    else raiseParseError "foo"

char :: Char -> IO ()
char c = do
  s <- readIORef text
  case T.uncons s of
    Nothing ->
      raiseParseError $
        "unexpected end of input\nexpecting: '" <> T.singleton c <> "'"
    Just (c', rest)
      | c == c' ->
        if c `S.member` newlineSet
          then updateStreamL rest
          else updateStreamC 1 rest
      | otherwise ->
        raiseParseError $
          "unexpected character: '"
            <> T.singleton c'
            <> "'\nexpecting: '"
            <> T.singleton c
            <> "'"

skip :: IO ()
skip = do
  s <- readIORef text
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

comment :: IO ()
comment = do
  s <- readIORef text
  case T.uncons s of
    Just (c, rest)
      | c `S.member` newlineSet ->
        updateStreamL rest >> skip
      | otherwise ->
        updateStreamC 1 rest >> comment
    Nothing ->
      return ()

many :: IO a -> IO [a]
many f =
  sepEndBy f (return ())

(<|>) :: IO a -> IO a -> IO a
(<|>) f g = do
  s <- readIORef text
  catch f (helper s g)

helper :: T.Text -> IO a -> Error -> IO a
helper s g _ = do
  writeIORef text s
  g

sepEndBy :: IO a -> IO () -> IO [a]
sepEndBy f g =
  sepEndBy' (f >>= return . Right) g []

sepEndBy' :: IO (Either [a] a) -> IO () -> [a] -> IO [a]
sepEndBy' f g acc = do
  itemOrResult <- catch f (finalize acc)
  g
  case itemOrResult of
    Right item ->
      sepEndBy' f g (item : acc)
    Left result ->
      return result

finalize :: [a] -> Error -> IO (Either [a] a)
finalize acc _ =
  return $ Left $ reverse acc

symbol :: IO T.Text
symbol = do
  s <- readIORef text
  let x = T.takeWhile isSymbolChar s
  let rest = T.dropWhile isSymbolChar s
  updateStreamC (T.length x) rest
  if T.null x
    then raiseParseError "empty symbol"
    else return x

string :: IO T.Text
string = do
  s <- readIORef text
  len <- headStringLengthOf False s 1
  let (x, s') = T.splitAt len s
  modifyIORef' text $ \_ -> s'
  return x

  -- let rest = T.tail s -- T.head s is known to be '"'
  -- len <- headStringLengthOf False rest 1
  -- let (x, rest') = T.splitAt len s
  -- modifyIORef' text $ \_ -> rest'
  -- return x


headStringLengthOf :: EscapeFlag -> T.Text -> Int -> IO Int
headStringLengthOf flag s i =
  case T.uncons s of
    Nothing ->
      raiseParseError "unexpected end of input while parsing string"
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

currentHint :: IO Hint
currentHint = do
  l <- readIORef line
  c <- readIORef column
  path <- getCurrentFilePath
  return $ newHint (fromEnum l) (fromEnum c) path

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
  S.fromList $ "() \"\n;"

{-# INLINE updateStreamL #-}
updateStreamL :: T.Text -> IO ()
updateStreamL s = do
  modifyIORef' text $ \_ -> s
  incrementLine

{-# INLINE updateStreamC #-}
updateStreamC :: Int -> T.Text -> IO ()
updateStreamC c s = do
  modifyIORef' text $ \_ -> s
  modifyIORef' column $ \x -> c + x

{-# INLINE incrementLine #-}
incrementLine :: IO ()
incrementLine = do
  modifyIORef' line $ \x -> 1 + x
  modifyIORef' column $ \_ -> 1

{-# INLINE incrementColumn #-}
incrementColumn :: IO ()
incrementColumn =
  modifyIORef' column $ \x -> 1 + x

raiseParseError :: T.Text -> IO a
raiseParseError txt = do
  m <- currentHint
  throw $ Error [logError (getPosInfo m) txt]

isKeyword :: T.Text -> Bool
isKeyword s =
  s `elem` ["define", "-", "with", "let", "let?", "in", "match", "new", "match-noetic", "->"]


-- {-# INLINE readMacroMap #-}
-- readMacroMap :: Map.HashMap Char T.Text
-- readMacroMap =
--   Map.fromList
--     [ ('`', "quote"),
--       (',', "unquote"),
--       ('@', "splice")
--     ]
