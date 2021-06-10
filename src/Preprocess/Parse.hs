module Preprocess.Parse
  ( parse,
  )
where

import Control.Exception.Safe
import Data.Basic
import Data.Global
import Data.IORef
import Data.Log
import Data.PreTerm
import qualified Data.Set as S
import qualified Data.Text as T
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
term =
  do
    termPi
    <|> termPiIntro
    <|> termEnumElim
    <|> termQuestion
    <|> termCase
    <|> termCaseNoetic
    <|> termCocase
    <|> termLet
    <|> termLetCoproduct
    <|> termIf
    <|> termPiElim
    <|> termString
    <|> termSymbol

termPi :: IO PreTermPlus
termPi = do
  m <- currentHint
  token "pi"
  varList <- many ascription
  char '.' >> skip
  e <- term
  return (m, PreTermPi varList e)

termPiIntro :: IO PreTermPlus
termPiIntro = do
  m <- currentHint
  token "lambda"
  varList <- many ascription
  char '.' >> skip
  e <- term
  return (m, PreTermPiIntro varList e)

termPiElim :: IO PreTermPlus
termPiElim = do
  m <- currentHint
  e1 <- termSimple
  e2 <- termSimple
  es <- sepEndBy termSimple skip
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
termParen =
  inParen term

termEnumElim :: IO PreTermPlus
termEnumElim = do
  m <- currentHint
  token "switch"
  e <- term
  token "with"
  clauseList <- many enumClause
  token "end"
  return (m, PreTermEnumElim e clauseList)

enumClause :: IO (T.Text, PreTermPlus)
enumClause = do
  flag <- lookAheadSymbol "end"
  if flag
    then raiseParseError "end"
    else do
      token "-"
      c <- symbol
      token "->"
      body <- term
      skip
      return (c, body)

termQuestion :: IO PreTermPlus
termQuestion = do
  m <- currentHint
  token "question"
  e <- term
  return (m, PreTermQuestion e)

termCase :: IO PreTermPlus
termCase = do
  m <- currentHint
  token "match"
  e <- term
  token "with"
  clauseList <- many caseClause
  token "end"
  return (m, PreTermCase False e clauseList)

termCaseNoetic :: IO PreTermPlus
termCaseNoetic = do
  m <- currentHint
  token "match-noetic"
  e <- term
  token "with"
  clauseList <- many caseClause
  token "end"
  return (m, PreTermCase True e clauseList)

caseClause :: IO (PrePattern, PreTermPlus)
caseClause = do
  flag <- lookAheadSymbol "end"
  if flag
    then raiseParseError "end"
    else do
      token "-"
      c <- pat
      body <- term
      skip
      return (c, body)

pat :: IO PrePattern
pat = do
  m <- currentHint
  c <- symbol
  argList <- patArg
  return (m, c, argList)

patArg :: IO [T.Text]
patArg = do
  x <- symbol
  skip
  if x == "->"
    then return []
    else do
      tmp <- patArg
      return $ x : tmp

termCocase :: IO PreTermPlus
termCocase = do
  m <- currentHint
  token "new"
  x <- symbol
  token "with"
  clauseList <- many $ do
    token "-"
    c <- symbol
    token "<-"
    body <- term
    return (c, body)
  return (m, PreTermCocase x clauseList)

-- (x : A)
ascription :: IO PreIdentPlus
ascription = do
  m <- currentHint
  inParen $ do
    x <- symbol
    char ':'
    skip
    a <- term
    return (m, x, a)

inParen :: IO a -> IO a
inParen f = do
  char '(' >> skip
  item <- f
  char ')' >> skip
  return item

termLet :: IO PreTermPlus
termLet = do
  m <- currentHint
  token "let"
  x <- symbol
  char '='
  skip
  e1 <- term
  token "in"
  e2 <- term
  return (m, PreTermLet x e1 e2)

termLetCoproduct :: IO PreTermPlus
termLetCoproduct = do
  m <- currentHint
  token "let?"
  x <- symbol
  char '='
  skip
  e1 <- term
  token "in"
  e2 <- term
  return (m, PreTermLetCoproduct x e1 e2)

termIf :: IO PreTermPlus
termIf = do
  m <- currentHint
  token "if"
  e1 <- term
  token "then"
  e2 <- term
  token "else"
  e3 <- term
  token "end"
  return (m, PreTermIf e1 e2 e3)

termSymbol :: IO PreTermPlus
termSymbol = do
  m <- currentHint
  x <- symbol
  if isKeyword x
    then raiseParseError $ "found a keyword `" <> x <> "`, expecting a symbol"
    else return (m, PreTermSymbol x)

token :: T.Text -> IO ()
token expected = do
  actual <- symbol
  if actual == expected
    then return ()
    else raiseParseError $ "found an unexpected token `" <> actual <> "`, expecting: " <> expected

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

lookAheadSymbol :: T.Text -> IO Bool
lookAheadSymbol atom = do
  s <- readIORef text
  headSymbol <- symbol
  writeIORef text s
  return $ headSymbol == atom

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
  skip
  if T.null x
    then raiseParseError "empty symbol"
    else return x

string :: IO T.Text
string = do
  s <- readIORef text
  len <- headStringLengthOf False s 1
  let (x, s') = T.splitAt len s
  modifyIORef' text $ \_ -> s'
  skip
  return x

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
  s `elem` ["define", "-", "with", "let", "let?", "in", "match", "new", "match-noetic", "->", "end"]
