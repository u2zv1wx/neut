{-# LANGUAGE OverloadedStrings #-}

module Complete
  ( complete
  ) where

import Control.Monad.State
import Data.List
import Path

import qualified Data.HashMap.Strict as Map
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

import Data.Basic
import Data.Env
import Data.WeakTerm
import Parse
import Parse.Tokenize

type CompInfo = [(Identifier, Meta)]

type CursorName = Identifier

type Prefix = T.Text

complete :: Path Abs File -> Line -> Column -> WithEnv [String]
complete inputPath l c = do
  info <- parseForCompletion inputPath l c
  return $ showCompInfo info

showCompInfo :: CompInfo -> [String]
showCompInfo [] = []
showCompInfo ((x, m):xms) = do
  let (path, (_, l, c)) = getPosInfo m
  let pathStr = "\"" <> toFilePath path <> "\""
  let x' = T.unpack $ asText x
  let str =
        "(\"" ++
        x' ++ "\" (" ++ pathStr ++ " " ++ show l ++ " " ++ show c ++ "))"
  str : showCompInfo xms

parseForCompletion :: Path Abs File -> Line -> Column -> WithEnv CompInfo
parseForCompletion path l c = do
  pushTrace path
  modify (\env -> env {fileEnv = Map.insert path VisitInfoActive (fileEnv env)})
  modify (\env -> env {phase = 1 + phase env})
  content <- liftIO $ TIO.readFile $ toFilePath path
  let s = I ("*cursor*", 0)
  case modifyFileForCompletion s content l c of
    Nothing -> do
      return []
    Just (prefix, content') -> do
      treeList <- tokenize content'
      stmtList <- parse' $ includeCore (newMeta 1 1 path) treeList
      case compInfo s stmtList of
        Right () -> return []
        Left info -> do
          info' <- filterM (filterCompInfo prefix) $ concatMap enrich info
          let compareLoc m1 m2 = metaLocation m2 `compare` metaLocation m1
          return $ nub $ sortBy (\(_, m1) (_, m2) -> compareLoc m1 m2) info'

modifyFileForCompletion ::
     CursorName -> T.Text -> Line -> Column -> Maybe (Prefix, T.Text)
modifyFileForCompletion (I (s, _)) content l c = do
  let xs = T.lines content
  let (ys, ws) = splitAt (l - 1) xs
  (targetLine, zs) <- headTailMaybe ws
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

compInfo :: CursorName -> [QuasiStmt] -> Either CompInfo ()
compInfo c ss = compInfoQuasiStmtList c [] ss

compInfoQuasiStmtList ::
     CursorName -> CompInfo -> [QuasiStmt] -> Either CompInfo ()
compInfoQuasiStmtList _ _ [] = return ()
compInfoQuasiStmtList c info ((QuasiStmtLet _ (mx, x, t) e):ss) = do
  compInfoWeakTermPlus c info t
  let info' = (x, mx) : info
  compInfoWeakTermPlus c info' e
  compInfoQuasiStmtList c info' ss
compInfoQuasiStmtList c info ((QuasiStmtDef xds):ss) = do
  xms <- mapM (compInfoDef c info . snd) xds
  let info' = xms ++ info
  compInfoQuasiStmtList c info' ss
compInfoQuasiStmtList c info ((QuasiStmtConstDecl _ (mx, x, t)):ss) = do
  compInfoWeakTermPlus c info t
  let info' = (x, mx) : info
  compInfoQuasiStmtList c info' ss
compInfoQuasiStmtList c info (_:ss) = compInfoQuasiStmtList c info ss

compInfoDef ::
     CursorName -> CompInfo -> Def -> Either CompInfo (Identifier, Meta)
compInfoDef c info (_, (mx, x, t), xts, e) = do
  compInfoWeakTermPlus c info t
  let info' = (x, mx) : info
  compInfoBinder c info' xts e
  return (x, mx)

compInfoWeakTermPlus ::
     CursorName -> CompInfo -> WeakTermPlus -> Either CompInfo ()
compInfoWeakTermPlus _ _ (_, WeakTermTau) = return ()
compInfoWeakTermPlus c info (_, WeakTermUpsilon x)
  | asText c == asText x = Left info
  | otherwise = return ()
compInfoWeakTermPlus c info (_, WeakTermPi _ xts t) =
  compInfoBinder c info xts t
compInfoWeakTermPlus c info (_, WeakTermPiIntro xts e) =
  compInfoBinder c info xts e
compInfoWeakTermPlus c info (_, WeakTermPiIntroNoReduce xts e) =
  compInfoBinder c info xts e
compInfoWeakTermPlus c info (_, WeakTermPiIntroPlus _ _ xts e) =
  compInfoBinder c info xts e
compInfoWeakTermPlus c info (_, WeakTermPiElim e es) = do
  mapM_ (compInfoWeakTermPlus c info) es
  compInfoWeakTermPlus c info e
compInfoWeakTermPlus c info (_, WeakTermIter (mx, x, t) xts e) = do
  compInfoWeakTermPlus c info t
  let info' = (x, mx) : info
  compInfoBinder c info' xts e
compInfoWeakTermPlus _ _ (_, WeakTermZeta _) = return ()
compInfoWeakTermPlus _ _ (_, WeakTermConst _) = return ()
compInfoWeakTermPlus c info (_, WeakTermInt t _) = compInfoWeakTermPlus c info t
compInfoWeakTermPlus _ _ (_, WeakTermFloat16 _) = return ()
compInfoWeakTermPlus _ _ (_, WeakTermFloat32 _) = return ()
compInfoWeakTermPlus _ _ (_, WeakTermFloat64 _) = return ()
compInfoWeakTermPlus c info (_, WeakTermFloat t _) =
  compInfoWeakTermPlus c info t
compInfoWeakTermPlus _ _ (_, WeakTermEnum _) = return ()
compInfoWeakTermPlus _ _ (_, WeakTermEnumIntro _) = return ()
compInfoWeakTermPlus c info (_, WeakTermEnumElim (e, _) les) = do
  compInfoWeakTermPlus c info e
  let (_, es) = unzip les
  mapM_ (compInfoWeakTermPlus c info) es
compInfoWeakTermPlus c info (_, WeakTermArray dom _) =
  compInfoWeakTermPlus c info dom
compInfoWeakTermPlus c info (_, WeakTermArrayIntro _ es) =
  mapM_ (compInfoWeakTermPlus c info) es
compInfoWeakTermPlus c info (_, WeakTermArrayElim _ xts e1 e2) = do
  compInfoWeakTermPlus c info e1
  compInfoBinder c info xts e2
compInfoWeakTermPlus _ _ (_, WeakTermStruct _) = return ()
compInfoWeakTermPlus c info (_, WeakTermStructIntro eks) = do
  let es = map fst eks
  mapM_ (compInfoWeakTermPlus c info) es
compInfoWeakTermPlus c info (_, WeakTermStructElim mxks e1 e2) = do
  compInfoWeakTermPlus c info e1
  compInfoArrayElim c info mxks e2
compInfoWeakTermPlus c info (_, WeakTermCase _ e cxtes) = do
  compInfoWeakTermPlus c info e
  forM_ cxtes $ \((_, xts), body) -> compInfoBinder c info xts body
compInfoWeakTermPlus c info (_, WeakTermWithNote e t) = do
  compInfoWeakTermPlus c info e
  compInfoWeakTermPlus c info t

compInfoBinder ::
     CursorName
  -> CompInfo
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> Either CompInfo ()
compInfoBinder s info [] e = compInfoWeakTermPlus s info e
compInfoBinder s info ((mx, x, t):xts) e = do
  compInfoWeakTermPlus s info t
  let info' = (x, mx) : info
  compInfoBinder s info' xts e

compInfoArrayElim ::
     CursorName
  -> CompInfo
  -> [(Meta, Identifier, ArrayKind)]
  -> WeakTermPlus
  -> Either CompInfo ()
compInfoArrayElim s info [] e = compInfoWeakTermPlus s info e
compInfoArrayElim s info ((mx, x, _):xts) e = do
  let info' = (x, mx) : info
  compInfoArrayElim s info' xts e

filterCompInfo :: Prefix -> (Identifier, Meta) -> WithEnv Bool
filterCompInfo _ (I (x, _), _)
  | "private:" `T.isPrefixOf` x = return False
filterCompInfo prefix (I (x, _), _) = do
  nenv <- gets nonCandSet
  return $ prefix `T.isPrefixOf` x && not (S.member x nenv)

enrich :: (Identifier, Meta) -> [(Identifier, Meta)]
enrich (x, m) = map (\y -> (y, m)) $ toSuffixList x

-- "bar:buz:qux" ~> ["bar:buz:qux", "buz:qux", "qux"]
toSuffixList :: Identifier -> [Identifier]
toSuffixList (I (s, i)) = map (\x -> I (x, i)) $ toSuffixList' s

toSuffixList' :: T.Text -> [T.Text]
toSuffixList' s =
  case T.findIndex (== ':') s of
    Nothing -> [s]
    Just i -> s : toSuffixList' (T.drop (i + 1) s)

headTailMaybe :: [a] -> Maybe (a, [a])
headTailMaybe [] = Nothing
headTailMaybe (x:xs) = return (x, xs)

headTailMaybeText :: T.Text -> Maybe (Char, T.Text)
headTailMaybeText s
  | s == T.empty = Nothing
  | otherwise = return (T.head s, T.tail s)

splitAtMaybe :: Int -> T.Text -> Maybe (T.Text, T.Text)
splitAtMaybe i xs = do
  if 0 <= i && i < T.length xs
    then return $ T.splitAt i xs
    else Nothing
