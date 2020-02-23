{-# LANGUAGE OverloadedStrings #-}

module Parse.Read
  ( strToTree
  ) where

import Control.Monad.Except
import Control.Monad.State
import Path

import qualified Data.IntMap.Strict as IntMap
import qualified Data.Set as S
import qualified Data.Text as T

import Data.Basic
import Data.Env
import Data.Tree

data ReadEnv =
  ReadEnv
    { text :: T.Text
    , line :: Int
    , column :: Int
    , filePath :: Path Abs File
    }
  deriving (Show)

type WithReadEnv a = StateT ReadEnv (ExceptT T.Text IO) a

strToTree :: T.Text -> Path Abs File -> WithEnv [TreePlus]
strToTree input path = do
  modify (\env -> env {count = 1 + count env})
  let renv = ReadEnv {text = input, line = 0, column = 0, filePath = path}
  resultOrError <- liftIO $ runExceptT (runStateT readSExpList renv)
  case resultOrError of
    Left err -> throwError' $ T.pack (show err)
    Right (result, _) -> return result

readSExpList :: WithReadEnv [TreePlus]
readSExpList = readSkip >> readSepEndBy readSExp readSkip

readSExp :: WithReadEnv TreePlus
readSExp = do
  s <- gets text
  case T.uncons s of
    Just ('(', _) -> readNode
    _ -> readAtom

readAtom :: WithReadEnv TreePlus
readAtom = do
  m <- currentMeta
  x <- readSymbol
  readSkip
  return (m, TreeAtom x)

readNode :: WithReadEnv TreePlus
readNode = do
  m <- currentMeta
  readChar '(' >> readSkip
  itemList <- readMany readSExp
  readSkip >> readChar ')' >> readSkip
  return (m, TreeNode itemList)

readChar :: Char -> WithReadEnv ()
readChar c = do
  s <- gets text
  case T.uncons s of
    Nothing -> throwError "hey"
    Just (c', rest)
      | c == c' -> do
        if c == '\n'
          then updateStreamL rest
          else updateStreamC 1 rest
      | otherwise -> throwError "non-expected char!"

readSkip :: WithReadEnv ()
readSkip = do
  readSpace
  s <- gets text
  case T.uncons s of
    Just (';', _) -> readComment
    _ -> readSpace

readSpace :: WithReadEnv ()
readSpace = do
  s <- gets text
  case T.uncons s of
    Just (c, rest)
      | c `S.member` spaceSet -> updateStreamC 1 rest >> readSpace
      | c `S.member` newlineSet -> updateStreamL rest >> readSpace
    _ -> return ()

readComment :: WithReadEnv ()
readComment = do
  s <- gets text
  case T.uncons s of
    Just ('\n', rest) -> updateStreamL rest >> readSkip
    Just (_, rest) -> updateStreamC 1 rest >> readComment
    Nothing -> throwError "comment"

readMany :: WithReadEnv a -> WithReadEnv [a]
readMany f = readSepEndBy f (return ())

readSepEndBy :: WithReadEnv a -> WithReadEnv () -> WithReadEnv [a]
readSepEndBy f g = readSepEndBy' (f >>= return . Right) g []

readSepEndBy' ::
     WithReadEnv (Either [a] a) -> WithReadEnv () -> [a] -> WithReadEnv [a]
readSepEndBy' f g acc = do
  itemOrResult <- catchError f (const $ return $ Left $ reverse acc)
  g
  case itemOrResult of
    Right item -> readSepEndBy' f g (item : acc)
    Left result -> return result

-- fixme: 本当は文字列もちゃんとreadできるようにするべき
readSymbol :: WithReadEnv T.Text
readSymbol = do
  s <- gets text
  let x = T.takeWhile isSymbolChar s
  if T.null x
    then throwError "sym"
    else do
      let rest = T.dropWhile isSymbolChar s
      updateStreamC (T.length x) rest
      return x

currentMeta :: WithReadEnv Meta
currentMeta = do
  l <- gets line
  c <- gets column
  path <- gets filePath
  return $
    Meta
      { metaFileName = Just path
      , metaLocation = Just (0, l, c)
      , metaConstraintLocation = Just (0, l, c)
      , metaIsPublic = True
      , metaIsAppropriateAsCompletionCandidate = True
      , metaUnivParams = IntMap.empty
      }

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
nonSymbolSet = S.fromList "()[] \n;"

{-# INLINE updateStreamL #-}
updateStreamL :: T.Text -> WithReadEnv ()
updateStreamL s = modify (\env -> env {text = s, column = 1 + column env})

{-# INLINE updateStreamC #-}
updateStreamC :: Int -> T.Text -> WithReadEnv ()
updateStreamC l s =
  modify (\env -> env {text = s, line = l + line env, column = 0})
