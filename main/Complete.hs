module Complete
  ( complete,
  )
where

import Control.Monad.State.Lazy
import Data.Basic
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.List hiding (findIndex)
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.WeakTerm
import Parse
import Parse.Tokenize
import Path

type CompInfo = [(Ident, Meta)]

type CursorName = Ident

type Prefix = T.Text

complete :: Path Abs File -> Line -> Column -> WithEnv [String]
complete inputPath l c = do
  info <- parseForCompletion inputPath l c
  return $ showCompInfo info

showCompInfo :: CompInfo -> [String]
showCompInfo [] = []
showCompInfo ((x, m) : xms) = do
  let (path, (_, l, c)) = getPosInfo m
  let pathStr = "\"" <> toFilePath path <> "\""
  let x' = T.unpack $ asText x
  let str = "(\"" ++ x' ++ "\" (" ++ pathStr ++ " " ++ show l ++ " " ++ show c ++ "))"
  str : showCompInfo xms

parseForCompletion :: Path Abs File -> Line -> Column -> WithEnv CompInfo
parseForCompletion path l c = do
  pushTrace path
  modify (\env -> env {fileEnv = Map.insert path VisitInfoActive (fileEnv env)})
  modify (\env -> env {phase = 1 + phase env})
  content <- liftIO $ TIO.readFile $ toFilePath path
  let s = I ("*cursor*", 0)
  case modifyFileForCompletion s content l c of
    Nothing -> return []
    Just (prefix, content') -> do
      treeList <- tokenize content'
      stmtList <- parse' $ includeCore (newMeta 1 1 path) treeList
      case compInfo s stmtList of
        Right () -> return []
        Left info -> do
          let info' = filter (filterCompInfo prefix) $ concatMap enrich info
          let compareLoc m1 m2 = metaLocation m2 `compare` metaLocation m1
          return $ nub $ sortBy (\(_, m1) (_, m2) -> compareLoc m1 m2) info'

modifyFileForCompletion ::
  CursorName -> T.Text -> Line -> Column -> Maybe (Prefix, T.Text)
modifyFileForCompletion (I (s, _)) content l c = do
  let xs = T.lines content
  let (ys, ws) = splitAt (l - 1) xs
  (targetLine, zs) <- uncons ws
  (s1, s2) <- splitAtMaybe (c - 1) targetLine
  (ch, s2') <- headTailMaybeText s2
  case ch of
    '(' -> Nothing
    ')' -> do
      let targetLine' = s1 <> " " <> s <> s2
      return (T.empty, T.unlines $ ys ++ [targetLine'] ++ zs)
    ' ' -> do
      let targetLine' = s1 <> " " <> s <> s2
      return (T.empty, T.unlines $ ys ++ [targetLine'] ++ zs)
    _ -> do
      let baseStr = s1 <> T.singleton ch
      let revBaseStr = T.reverse baseStr
      let revPrefix = T.takeWhile (`notElem` ['(', ' ', ')']) revBaseStr
      let prefix = T.reverse revPrefix
      let revStr = T.dropWhile (`notElem` ['(', ' ', ')']) revBaseStr
      let s1' = T.reverse revStr
      let s2'' = T.dropWhile (`notElem` ['(', ' ', ')']) s2'
      let targetLine' = s1' <> s <> s2''
      return (prefix, T.unlines $ ys ++ [targetLine'] ++ zs)

compInfo :: CursorName -> [WeakStmt] -> Either CompInfo ()
compInfo c = compInfoWeakStmtList c []

compInfoWeakStmtList :: CursorName -> CompInfo -> [WeakStmt] -> Either CompInfo ()
compInfoWeakStmtList c info stmtList =
  case stmtList of
    [] ->
      return ()
    WeakStmtLet _ (mx, x, t) e : ss -> do
      compInfoWeakTermPlus c info t
      let info' = (x, mx) : info
      compInfoWeakTermPlus c info' e
      compInfoWeakStmtList c info' ss
    _ : ss ->
      compInfoWeakStmtList c info ss

compInfoWeakTermPlus :: CursorName -> CompInfo -> WeakTermPlus -> Either CompInfo ()
compInfoWeakTermPlus c info term =
  case term of
    (_, WeakTermTau) ->
      return ()
    (_, WeakTermUpsilon x)
      | asText c == asText x ->
        Left info
      | otherwise ->
        return ()
    (_, WeakTermPi _ xts t) ->
      compInfoBinder c info xts t
    (_, WeakTermPiIntro _ xts e) ->
      compInfoBinder c info xts e
    (_, WeakTermPiElim e es) -> do
      mapM_ (compInfoWeakTermPlus c info) es
      compInfoWeakTermPlus c info e
    (_, WeakTermIter (mx, x, t) xts e) -> do
      compInfoWeakTermPlus c info t
      let info' = (x, mx) : info
      compInfoBinder c info' xts e
    (_, WeakTermZeta _) ->
      return ()
    (_, WeakTermConst _) ->
      return ()
    (_, WeakTermBoxElim _) ->
      return ()
    (_, WeakTermInt t _) ->
      compInfoWeakTermPlus c info t
    (_, WeakTermFloat t _) ->
      compInfoWeakTermPlus c info t
    (_, WeakTermEnum _) ->
      return ()
    (_, WeakTermEnumIntro _) ->
      return ()
    (_, WeakTermEnumElim (e, _) les) -> do
      compInfoWeakTermPlus c info e
      let (_, es) = unzip les
      mapM_ (compInfoWeakTermPlus c info) es
    (_, WeakTermArray dom _) ->
      compInfoWeakTermPlus c info dom
    (_, WeakTermArrayIntro _ es) ->
      mapM_ (compInfoWeakTermPlus c info) es
    (_, WeakTermArrayElim _ xts e1 e2) -> do
      compInfoWeakTermPlus c info e1
      compInfoBinder c info xts e2
    (_, WeakTermStruct _) ->
      return ()
    (_, WeakTermStructIntro eks) -> do
      let es = map fst eks
      mapM_ (compInfoWeakTermPlus c info) es
    (_, WeakTermStructElim mxks e1 e2) -> do
      compInfoWeakTermPlus c info e1
      compInfoArrayElim c info mxks e2
    (_, WeakTermCase _ e cxtes) -> do
      compInfoWeakTermPlus c info e
      forM_ cxtes $ \((_, xts), body) -> compInfoBinder c info xts body
    (_, WeakTermQuestion e t) -> do
      compInfoWeakTermPlus c info e
      compInfoWeakTermPlus c info t
    (_, WeakTermErase _ e) ->
      compInfoWeakTermPlus c info e

compInfoBinder ::
  CursorName ->
  CompInfo ->
  [WeakIdentPlus] ->
  WeakTermPlus ->
  Either CompInfo ()
compInfoBinder s info binder e =
  case binder of
    [] ->
      compInfoWeakTermPlus s info e
    (mx, x, t) : xts -> do
      compInfoWeakTermPlus s info t
      let info' = (x, mx) : info
      compInfoBinder s info' xts e

compInfoArrayElim ::
  CursorName ->
  CompInfo ->
  [(Meta, Ident, ArrayKind)] ->
  WeakTermPlus ->
  Either CompInfo ()
compInfoArrayElim s info binder e =
  case binder of
    [] ->
      compInfoWeakTermPlus s info e
    (mx, x, _) : xts -> do
      let info' = (x, mx) : info
      compInfoArrayElim s info' xts e

filterCompInfo :: Prefix -> (Ident, Meta) -> Bool
filterCompInfo prefix (I (x, _), _)
  | "private:" `T.isPrefixOf` x =
    False
  | otherwise =
    prefix `T.isPrefixOf` x && T.all (`S.notMember` S.fromList "()") x

enrich :: (Ident, Meta) -> [(Ident, Meta)]
enrich (x, m) = map (\y -> (y, m)) $ toSuffixList x

-- "bar:buz:qux" ~> ["bar:buz:qux", "buz:qux", "qux"]
toSuffixList :: Ident -> [Ident]
toSuffixList (I (s, i)) = map (\x -> I (x, i)) $ toSuffixList' s

toSuffixList' :: T.Text -> [T.Text]
toSuffixList' s =
  case T.findIndex (== ':') s of
    Nothing ->
      [s]
    Just i ->
      s : toSuffixList' (T.drop (toEnum i + 1) s)

headTailMaybeText :: T.Text -> Maybe (Char, T.Text)
headTailMaybeText s
  | s == T.empty = Nothing
  | otherwise = return (T.head s, T.tail s)

splitAtMaybe :: Int -> T.Text -> Maybe (T.Text, T.Text)
splitAtMaybe i xs =
  if 0 <= i && toEnum i < T.length xs
    then return $ T.splitAt (toEnum i) xs
    else Nothing
