module Complete
  ( complete,
  )
where

import Control.Monad.State.Lazy
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Ident
import Data.List hiding (findIndex)
import Data.Meta
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Parse
import Parse.Tokenize
import Path

type CursorName =
  Ident

complete :: Path Abs File -> Line -> Column -> WithEnv ()
complete =
  parseForCompletion

parseForCompletion :: Path Abs File -> Line -> Column -> WithEnv ()
parseForCompletion path l c = do
  pushTrace path
  modify (\env -> env {fileEnv = Map.insert path VisitInfoActive (fileEnv env)})
  modify (\env -> env {phase = 1 + phase env})
  content <- liftIO $ TIO.readFile $ toFilePath path
  let s = I ("*cursor*", 0)
  case modifyFileForCompletion s content l c of
    Nothing ->
      return ()
    Just content' -> do
      treeList <- tokenize content'
      void $ parse' $ includeCore (newMeta 1 1 path) treeList

modifyFileForCompletion :: CursorName -> T.Text -> Line -> Column -> Maybe T.Text
modifyFileForCompletion (I (s, _)) content l c = do
  let xs = T.lines content
  let (ys, ws) = splitAt (l - 1) xs
  (targetLine, zs) <- uncons ws
  (s1, s2) <- splitAtMaybe (c - 1) targetLine
  (ch, s2') <- T.uncons s2
  case ch of
    '(' ->
      Nothing
    ')' -> do
      let targetLine' = s1 <> " " <> s <> s2
      return $ T.unlines $ ys ++ [targetLine'] ++ zs
    ' ' -> do
      let targetLine' = s1 <> " " <> s <> s2
      return $ T.unlines $ ys ++ [targetLine'] ++ zs
    _ -> do
      let baseStr = s1 <> T.singleton ch
      let revBaseStr = T.reverse baseStr
      let revStr = T.dropWhile (`notElem` ['(', ' ', ')']) revBaseStr
      let s1' = T.reverse revStr
      let s2'' = T.dropWhile (`notElem` ['(', ' ', ')']) s2'
      let targetLine' = s1' <> s <> s2''
      return $ T.unlines $ ys ++ [targetLine'] ++ zs

splitAtMaybe :: Int -> T.Text -> Maybe (T.Text, T.Text)
splitAtMaybe i xs =
  if 0 <= i && toEnum i < T.length xs
    then return $ T.splitAt (toEnum i) xs
    else Nothing
