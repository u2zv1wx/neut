module Preprocess.Tokenize
  ( tokenize,
  )
where

import Control.Exception.Safe
import Data.Basic
import Data.Global
import qualified Data.HashMap.Lazy as Map
import Data.IORef
import Data.Log
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Tree
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

tokenize :: T.Text -> IO [TreePlus]
tokenize input = do
  modifyIORef' text $ \_ -> input
  program []

program :: [TreePlus] -> IO [TreePlus]
program acc = do
  skip
  s <- readIORef text
  if T.null s
    then return $ reverse acc
    else do
      t <- term
      program $ t : acc

term :: IO TreePlus
term = do
  s <- readIORef text
  case T.uncons s of
    Just (c, _)
      | Just l <- Map.lookup c readMacroMap ->
        resolveReadMacro c l
    Just ('(', _) ->
      node
    _ ->
      leaf

leaf :: IO TreePlus
leaf = do
  m <- currentHint
  s <- readIORef text
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

node :: IO TreePlus
node = do
  m <- currentHint
  char '(' >> skip
  itemList <- many term
  skip >> char ')' >> skip
  return (m, TreeNode itemList)

resolveReadMacro :: Char -> T.Text -> IO TreePlus
resolveReadMacro from to = do
  m <- currentHint
  char from >> skip
  item <- term
  skip
  return (m, TreeNode [(m, TreeLeaf to), item])

char :: Char -> IO ()
char c = do
  s <- readIORef text
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
  return x

string :: IO T.Text
string = do
  s <- readIORef text
  let rest = T.tail s -- T.head s is known to be '"'
  len <- headStringLengthOf False rest 1
  let (x, rest') = T.splitAt len s
  modifyIORef' text $ \_ -> rest'
  return x

headStringLengthOf :: EscapeFlag -> T.Text -> Int -> IO Int
headStringLengthOf flag s i =
  case T.uncons s of
    Nothing ->
      raiseTokenizeError "unexpected end of input while parsing string"
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
  S.fromList $ "() \"\n;" ++ map fst (Map.toList readMacroMap)

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

raiseTokenizeError :: T.Text -> IO a
raiseTokenizeError txt = do
  m <- currentHint
  throw $ Error [logError (getPosInfo m) txt]

{-# INLINE readMacroMap #-}
readMacroMap :: Map.HashMap Char T.Text
readMacroMap =
  Map.fromList
    [ ('`', "quote"),
      (',', "unquote"),
      ('@', "splice")
    ]
