module Parse.Core where

import Control.Exception.Safe
import Data.Basic
import Data.Global
import Data.IORef
import Data.Log
import qualified Data.Set as S
import qualified Data.Text as T
import Data.WeakTerm
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

--
-- basic functions for the parser combinator
--

type ParserState = (T.Text, Int, Int)

saveState :: IO ParserState
saveState = do
  s <- readIORef text
  l <- readIORef line
  c <- readIORef column
  return (s, l, c)

loadState :: ParserState -> IO ()
loadState (s, l, c) = do
  writeIORef text s
  writeIORef line l
  writeIORef column c

initializeState :: T.Text -> IO ()
initializeState fileContent = do
  writeIORef line 1
  writeIORef column 1
  writeIORef text fileContent

-- modifyIORef' text $ \_ -> content

withNestedState :: IO a -> IO a
withNestedState comp = do
  state <- saveState
  value <- comp
  loadState state
  return value

betweenParen :: IO a -> IO a
betweenParen f = do
  char '(' >> skip
  item <- f
  char ')' >> skip
  return item

token :: T.Text -> IO ()
token expected = do
  m <- currentHint
  actual <- symbol
  if actual == expected
    then return ()
    else raiseParseError m $ "found an unexpected token `" <> actual <> "`, expecting: " <> expected

char :: Char -> IO ()
char c = do
  m <- currentHint
  s <- readIORef text
  case T.uncons s of
    Nothing ->
      raiseParseError m $
        "unexpected end of input\nexpecting: '" <> T.singleton c <> "'"
    Just (c', rest)
      | c == c' ->
        if c `S.member` newlineSet
          then updateStreamL rest
          else updateStreamC 1 rest
      | otherwise ->
        raiseParseError m $
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
      | c == '-',
        Just ('-', _) <- T.uncons rest ->
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
many f = do
  tryPlanList
    [ do
        x <- f
        xs <- many f
        return $ x : xs,
      return []
    ]

many1 :: IO a -> IO [a]
many1 f = do
  item <- f
  itemList <- many f
  return $ item : itemList

tryPlanList :: [IO a] -> IO a
tryPlanList planList =
  case planList of
    [] -> do
      m <- currentHint
      raiseCritical m "Parse.Core.tryPlanList: this function shouldn't be called for the empty list"
    [f] ->
      f
    f : fs -> do
      s <- saveState
      catch f (helper s (tryPlanList fs))

helper :: ParserState -> IO a -> Error -> IO a
helper s g _ = do
  loadState s
  g

lookAhead :: IO a -> IO a
lookAhead f = do
  s <- saveState
  result <- f
  loadState s
  return result

sepBy2 :: IO a -> IO b -> IO [a]
sepBy2 f sep = do
  item1 <- f
  _ <- sep
  item2 <- f
  itemList <- many $ sep >> f
  return $ item1 : item2 : itemList

symbol :: IO T.Text
symbol = do
  m <- currentHint
  s <- readIORef text
  let x = T.takeWhile isSymbolChar s
  let rest = T.dropWhile isSymbolChar s
  updateStreamC (T.length x) rest
  skip
  if T.null x
    then raiseParseError m "unexpected non-symbol character, expecting: symbol-character"
    else return x

symbolMaybe :: IO (Maybe T.Text)
symbolMaybe = do
  s <- readIORef text
  let x = T.takeWhile isSymbolChar s
  let rest = T.dropWhile isSymbolChar s
  updateStreamC (T.length x) rest
  skip
  if T.null x
    then return Nothing
    else return $ Just x

simpleSymbol :: IO T.Text
simpleSymbol = do
  m <- currentHint
  s <- readIORef text
  let x = T.takeWhile isSimpleSymbolChar s
  let rest = T.dropWhile isSimpleSymbolChar s
  updateStreamC (T.length x) rest
  skip
  if T.null x
    then raiseParseError m "unexpected non-symbol character, expecting: symbol-character"
    else return x

string :: IO T.Text
string = do
  char '"'
  s <- readIORef text
  len <- stringLengthOf False s 0
  let (x, s') = T.splitAt len s
  writeIORef text $ T.tail s'
  skip
  return x

stringLengthOf :: EscapeFlag -> T.Text -> Int -> IO Int
stringLengthOf flag s i =
  case T.uncons s of
    Nothing -> do
      m <- currentHint
      raiseParseError m "unexpected end of input while parsing string"
    Just (c, rest)
      | c == '"' -> do
        incrementColumn
        if flag
          then stringLengthOf False rest (i + 1)
          else return i
      | c == '\\' -> do
        incrementColumn
        stringLengthOf (not flag) rest (i + 1)
      | c `S.member` newlineSet -> do
        incrementLine
        stringLengthOf False rest (i + 1)
      | otherwise -> do
        incrementColumn
        stringLengthOf False rest (i + 1)

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

{-# INLINE isSimpleSymbolChar #-}
isSimpleSymbolChar :: Char -> Bool
isSimpleSymbolChar c =
  c `S.notMember` nonSimpleSymbolSet

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
  S.fromList $ "() \"\n;,"

{-# INLINE nonSimpleSymbolSet #-}
nonSimpleSymbolSet :: S.Set Char
nonSimpleSymbolSet =
  S.insert '.' nonSymbolSet

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

raiseParseError :: Hint -> T.Text -> IO a
raiseParseError m txt =
  throw $ Error [logError (getPosInfo m) txt]

-- asKeyword :: T.Text -> Maybe Keywordみたいにすべきかも。
isKeyword :: T.Text -> Bool
isKeyword s =
  S.member s keywordSet

keywordSet :: S.Set T.Text
keywordSet =
  S.fromList
    [ "-",
      "->",
      ".",
      ":",
      "<-",
      "=",
      "?admit",
      "admit",
      "define",
      "define-codata",
      "define-data",
      "define-enum",
      "define-opaque",
      "define-prefix",
      "define-resource-type",
      "derangement",
      "do",
      "else",
      "else-if",
      "end",
      "ensure",
      "idealize",
      "if",
      "in",
      "include",
      "lambda",
      "let",
      "let?",
      "match",
      "match-noetic",
      "new",
      "over",
      "pi",
      "question",
      "reduce",
      "remove-prefix",
      "section",
      "switch",
      "tau",
      "then",
      "unuse",
      "use",
      "with"
    ]

weakVar :: Hint -> T.Text -> WeakTermPlus
weakVar m str =
  (m, WeakTermVar VarKindLocal (asIdent str))
