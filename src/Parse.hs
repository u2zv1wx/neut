{-# LANGUAGE OverloadedStrings #-}

module Parse
  ( parse
  , complete
  ) where

import Control.Monad.Except
import Control.Monad.State hiding (get)
import Data.ByteString.Builder
import Data.List
import Data.Maybe (catMaybes)
import Data.Monoid ((<>))
import Network.Http.Client
import Path
import Path.IO
import System.IO.Streams (InputStream)
import Text.Read (readMaybe)

import qualified Codec.Archive.Tar as Tar
import qualified Codec.Compression.GZip as GZip
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as L
import qualified Data.HashMap.Strict as Map
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import qualified System.IO.Streams as Streams

import Data.Basic
import Data.Env
import Data.Tree
import Data.WeakTerm
import Parse.Discern
import Parse.Interpret
import Parse.MacroExpand
import Parse.Rule
import Parse.Tokenize
import Parse.Utility

parse :: Path Abs File -> WithEnv WeakStmt
parse inputPath = do
  stmtList <- visit inputPath
  stmtList' <- discern stmtList
  pushTrace inputPath
  concatQuasiStmtList stmtList'

visit :: Path Abs File -> WithEnv [QuasiStmt]
visit path = do
  pushTrace path
  modify (\env -> env {fileEnv = Map.insert path VisitInfoActive (fileEnv env)})
  modify (\env -> env {phase = 1 + phase env})
  content <- liftIO $ TIO.readFile $ toFilePath path
  treeList <- tokenize content
  parse' $ includeCore (newMeta 1 1 path) treeList

leave :: WithEnv [QuasiStmt]
leave = do
  path <- getCurrentFilePath
  popTrace
  modify (\env -> env {fileEnv = Map.insert path VisitInfoFinish (fileEnv env)})
  modify (\env -> env {prefixEnv = []})
  return []

pushTrace :: Path Abs File -> WithEnv ()
pushTrace path = modify (\env -> env {traceEnv = path : traceEnv env})

popTrace :: WithEnv ()
popTrace = modify (\env -> env {traceEnv = tail (traceEnv env)})

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
parseForCompletion inputPath l c = do
  content <- liftIO $ TIO.readFile $ toFilePath inputPath
  s <- newNameWith' "cursor"
  case modifyFileForCompletion s content l c of
    Nothing -> return []
    Just (prefix, content') -> do
      stmtList <- tokenize content' >>= parse'
      case compInfo s stmtList of
        Right () -> return []
        Left info -> do
          info' <- filterM (filterCompInfo prefix) info
          let compareLoc m1 m2 = metaLocation m2 `compare` metaLocation m1
          return $ nub $ sortBy (\(_, m1) (_, m2) -> compareLoc m1 m2) info'

-- 必要ならここでprefixの情報も与える
-- parenとかのときは何も返さないからNothingにする
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

parse' :: [TreePlus] -> WithEnv [QuasiStmt]
parse' [] = leave
parse' ((m, TreeNode ((_, TreeLeaf "notation"):es)):as)
  | [from, to] <- es = do
    checkNotationSanity from
    modify (\e -> e {notationEnv = (from, to) : notationEnv e})
    parse' as
  | otherwise = raiseSyntaxError m "(notation TREE TREE)"
parse' ((m, TreeNode ((_, TreeLeaf "keyword"):es)):as)
  | [(_, TreeLeaf s)] <- es = do
    checkKeywordSanity m s
    modify (\e -> e {keywordEnv = S.insert s (keywordEnv e)})
    parse' as
  | otherwise = raiseSyntaxError m "(keyword LEAF)"
parse' ((m, TreeNode ((_, TreeLeaf "use"):es)):as)
  | [(_, TreeLeaf s)] <- es = do
    modify (\e -> e {prefixEnv = s : prefixEnv e}) -- required to check sanity of `include`
    stmtList <- parse' as
    return $ QuasiStmtUse s : stmtList
  | otherwise = raiseSyntaxError m "(use LEAF)"
parse' ((m, TreeNode ((_, TreeLeaf "unuse"):es)):as)
  | [(_, TreeLeaf s)] <- es = do
    modify (\e -> e {prefixEnv = filter (/= s) (prefixEnv e)}) -- required to check sanity of `include`
    stmtList <- parse' as
    return $ QuasiStmtUnuse s : stmtList
  | otherwise = raiseSyntaxError m "(unuse LEAF)"
parse' ((m, TreeNode ((_, TreeLeaf "section"):es)):as)
  | [(_, TreeLeaf s)] <- es = do
    modify (\e -> e {namespace = s : namespace e})
    n <- getCurrentSection
    stmtList <- parse' as
    return $ QuasiStmtUse n : stmtList -- auto-use
  | otherwise = raiseSyntaxError m "(section LEAF)"
parse' ((m, TreeNode ((_, TreeLeaf "end"):es)):as)
  | [(_, TreeLeaf s)] <- es = do
    ns <- gets namespace
    case ns of
      [] -> raiseError m "there is no section to end"
      (s':ns')
        | s == s' -> do
          n <- getCurrentSection
          modify (\e -> e {namespace = ns'})
          stmtList <- parse' as
          return $ QuasiStmtUnuse n : stmtList -- auto-unuse
        | otherwise ->
          raiseError m $
          "the innermost section is not `" <> s <> "`, but is `" <> s' <> "`"
  | otherwise = raiseSyntaxError m "(end LEAF)"
parse' ((m, TreeNode ((_, TreeLeaf "enum"):rest)):as)
  | (_, TreeLeaf name):ts <- rest = do
    xis <- interpretEnumItem m name ts
    m' <- adjustPhase m
    ss <- parse' as
    return $ QuasiStmtEnum m' name xis : ss
  | otherwise = raiseSyntaxError m "(enum LEAF TREE ... TREE)"
parse' ((m, TreeNode ((_, TreeLeaf "include"):rest)):as)
  | [(mPath, TreeLeaf pathString)] <- rest =
    includeFile m mPath pathString getCurrentDirPath as
  | [(_, TreeLeaf "library"), (mPath, TreeLeaf pathString)] <- rest =
    includeFile m mPath pathString getLibraryDirPath as
  | otherwise = raiseSyntaxError m "(include LEAF) | (include library LEAF)"
parse' ((m, TreeNode ((_, TreeLeaf "ensure"):rest)):as)
  | [(_, TreeLeaf pkg), (mUrl, TreeLeaf urlStr)] <- rest = do
    libDir <- getLibraryDirPath
    pkg' <- parseRelDir $ T.unpack pkg
    let path = libDir </> pkg'
    isAlreadyInstalled <- doesDirExist path
    when (not isAlreadyInstalled) $ do
      urlStr' <- parseByteString mUrl urlStr
      note $ "downloading " <> pkg <> " from " <> TE.decodeUtf8 urlStr'
      item <- liftIO $ get urlStr' lazyConcatHandler
      note $ "installing " <> pkg <> " into " <> T.pack (toFilePath path)
      install item path
    parse' as
  | otherwise = raiseSyntaxError m "(ensure LEAF LEAF)"
parse' ((m, TreeNode ((_, TreeLeaf "attribute"):rest)):as)
  | (_, TreeLeaf name):attrList <- rest = do
    ss1 <- mapM (parseAttr name) attrList
    ss2 <- parse' as
    return $ ss1 ++ ss2
  | otherwise = raiseSyntaxError m "(attribute LEAF TREE ... TREE)"
parse' ((_, TreeNode ((_, TreeLeaf "statement"):as1)):as2) = parse' $ as1 ++ as2
parse' ((m, TreeNode ((_, TreeLeaf "introspect"):rest)):as2)
  | ((mx, TreeLeaf x):stmtClauseList) <- rest = do
    val <- retrieveCompileTimeVarValue mx x
    stmtClauseList' <- mapM parseStmtClause stmtClauseList
    case lookup val stmtClauseList' of
      Nothing -> parse' as2
      Just as1 -> parse' $ as1 ++ as2
  | otherwise = raiseSyntaxError m "(introspect LEAF TREE*)"
parse' ((m, TreeNode ((_, TreeLeaf "constant"):rest)):as)
  | [(mn, TreeLeaf name), t] <- rest = do
    t' <- macroExpand t >>= interpret
    name' <- withSectionPrefix name
    cenv <- gets constantEnv
    case Map.lookup name' cenv of
      Just _ -> raiseError m $ "the constant " <> name' <> " is already defined"
      Nothing -> do
        i <- newCount
        modify (\e -> e {constantEnv = Map.insert name' i (constantEnv e)})
        defList <- parse' as
        m' <- adjustPhase m
        mn' <- adjustPhase mn
        return $ QuasiStmtConstDecl m' (mn', I (name', i), t') : defList
  | otherwise = raiseSyntaxError m "(constant LEAF TREE)"
parse' ((m, TreeNode (def@(mDef, TreeLeaf "definition"):rest)):as)
  | [name@(_, TreeLeaf _), body] <- rest =
    parse' $ (m, TreeNode [(mDef, TreeLeaf "let"), name, body]) : as
  | name@(mFun, TreeLeaf _):xts@(_, TreeNode _):body:rest' <- rest = do
    parse' $
      (m, TreeNode [def, (mFun, TreeNode (name : xts : body : rest'))]) : as
  | otherwise = do
    ss1 <- parseDef rest
    ss2 <- parse' as
    return $ ss1 ++ ss2
parse' ((m, TreeNode (ind@(_, TreeLeaf "inductive"):rest)):as)
  | name@(mFun, TreeLeaf _):xts@(_, TreeNode _):rest' <- rest = do
    parse' $ (m, TreeNode [ind, (mFun, TreeNode (name : xts : rest'))]) : as
  | otherwise = do
    rest' <- mapM macroExpand rest
    stmtList1 <- parseInductive m rest'
    stmtList2 <- parse' as
    return $ stmtList1 ++ stmtList2
parse' ((m, TreeNode (coind@(_, TreeLeaf "coinductive"):rest)):as)
  | name@(mFun, TreeLeaf _):xts@(_, TreeNode _):rest' <- rest = do
    parse' $ (m, TreeNode [coind, (mFun, TreeNode (name : xts : rest'))]) : as
  | otherwise = do
    rest' <- mapM macroExpand rest
    stmtList1 <- parseCoinductive m rest'
    stmtList2 <- parse' as
    return $ stmtList1 ++ stmtList2
parse' ((m, TreeNode ((mLet, TreeLeaf "let"):rest)):as)
  | [(mx, TreeLeaf x), t, e] <- rest = do
    let xt = (mx, TreeNode [(mx, TreeLeaf x), t])
    parse' ((m, TreeNode [(mLet, TreeLeaf "let"), xt, e]) : as)
  | [xt, e] <- rest = do
    xt' <- prefixIdentPlus xt
    m' <- adjustPhase m
    e' <- macroExpand e >>= interpret
    (mx, x, t) <- macroExpand xt' >>= interpretIdentifierPlus
    defList <- parse' as
    case e' of
      (_, WeakTermPiElim f args)
        | (mmxs, args') <- unzip $ map parseBorrow args
        , mxs <- catMaybes mmxs
        , not (null mxs) -> do
          xts <- mapM toIdentPlus mxs
          let app = (m, WeakTermPiElim f args')
          return $ QuasiStmtLetSigma m (xts ++ [(mx, x, t)]) app : defList
      _ -> return $ QuasiStmtLet m' (mx, x, t) e' : defList
  | otherwise = raiseSyntaxError m "(let LEAF TREE TREE) | (let TREE TREE)"
parse' (a:as) = do
  e <- macroExpand a
  if isSpecialForm e
    then parse' $ e : as
    else do
      e' <- interpret e
      case e' of
        (m, WeakTermPiElim f args)
          | (mmxs, args') <- unzip $ map parseBorrow args
          , mxs <- catMaybes mmxs
          , not (null mxs) -> do
            tmp <- newNameWith'' "borrow"
            xts <- mapM toIdentPlus $ mxs ++ [(m, tmp)]
            let app = (m, WeakTermPiElim f args')
            defList <- parse' as
            return $ QuasiStmtLetSigma m xts app : defList
        (m, _) -> do
          name <- newNameWith'' "hole"
          m' <- adjustPhase m
          t <- newHole m'
          defList <- parse' as
          modify
            (\env -> env {nonCandSet = S.insert (asText name) (nonCandSet env)})
          return $ QuasiStmtLet m' (m', name, t) e' : defList

lazyConcatHandler :: Response -> InputStream B.ByteString -> IO L.ByteString
lazyConcatHandler _ i1 = do
  i2 <- Streams.map byteString i1
  x <- Streams.fold mappend mempty i2
  return $ toLazyByteString x

withSectionPrefix :: T.Text -> WithEnv T.Text
withSectionPrefix x = do
  ns <- gets namespace
  return $ withSectionPrefix' ns x

withSectionPrefix' :: [T.Text] -> T.Text -> T.Text
withSectionPrefix' [] x = x
withSectionPrefix' (n:ns) x = withSectionPrefix' ns $ n <> ":" <> x

getCurrentSection :: WithEnv T.Text
getCurrentSection = do
  ns <- gets namespace
  return $ getCurrentSection' ns

getCurrentSection' :: [T.Text] -> T.Text
getCurrentSection' [] = ""
getCurrentSection' [n] = n
getCurrentSection' (n:ns) = getCurrentSection' ns <> ":" <> n

parseBorrow :: WeakTermPlus -> (Maybe (Meta, Identifier), WeakTermPlus)
parseBorrow (m, WeakTermUpsilon (I (s, _)))
  | T.length s > 1
  , T.head s == '&' =
    (Just (m, asIdent $ T.tail s), (m, WeakTermUpsilon $ asIdent $ T.tail s))
parseBorrow t = (Nothing, t)

parseByteString :: Meta -> T.Text -> WithEnv B.ByteString
parseByteString m quotedStr =
  case readMaybe (T.unpack quotedStr) of
    Nothing -> raiseError m "the argument of `include` must be a string"
    Just str -> return str

parseString :: Meta -> T.Text -> WithEnv String
parseString m quotedStr =
  case readMaybe (T.unpack quotedStr) of
    Nothing -> raiseError m "the argument of `include` must be a string"
    Just str -> return str

parseAttr :: T.Text -> TreePlus -> WithEnv QuasiStmt
parseAttr name (m, TreeNode [(_, TreeLeaf "implicit"), (_, TreeLeaf num)]) = do
  case readMaybe $ T.unpack num of
    Nothing -> raiseError m "the argument of `implicit` must be an integer"
    Just i -> return $ QuasiStmtImplicit m (asIdent name) i
parseAttr _ t = raiseError (fst t) $ "invalid attribute: " <> showAsSExp t

includeFile ::
     Meta
  -> Meta
  -> T.Text
  -> WithEnv (Path Abs Dir)
  -> [TreePlus]
  -> WithEnv [QuasiStmt]
includeFile m mPath pathString getDirPath as = do
  ensureEnvSanity m
  path <- parseString mPath pathString
  dirPath <- getDirPath
  newPath <- resolveFile dirPath path
  includeFile' m newPath as

includeFile' :: Meta -> Path Abs File -> [TreePlus] -> WithEnv [QuasiStmt]
includeFile' m path as = do
  ensureFileExistence m path
  denv <- gets fileEnv
  case Map.lookup path denv of
    Just VisitInfoActive -> reportCyclicPath m path
    Just VisitInfoFinish -> parse' as
    Nothing -> do
      includedQuasiStmtList <- visit path
      defList <- parse' as
      return $ includedQuasiStmtList ++ defList

ensureEnvSanity :: Meta -> WithEnv ()
ensureEnvSanity m = do
  ns <- gets namespace
  penv <- gets prefixEnv
  case (null ns, null penv) of
    (False, _) -> raiseError m "`include` can only be used at top-level section"
    (_, False) ->
      raiseError m "`include` can only be used with no prefix assumption"
    _ -> return ()

parseDef :: [TreePlus] -> WithEnv [QuasiStmt]
parseDef xds = do
  xds' <- mapM (prefixFunName >=> macroExpand) xds
  xs <- mapM extractFunName xds'
  (xds'', miss) <- unzip <$> mapM takeSquare xds'
  xds''' <- mapM interpretIter xds''
  let attrStmtList =
        concat $ zipWith (\x (m, is) -> map (QuasiStmtImplicit m x) is) xs miss
  return $ QuasiStmtDef (zip xs xds''') : attrStmtList

takeSquare :: TreePlus -> WithEnv (TreePlus, (Meta, [Int]))
takeSquare (m, TreeNode [xt, (mArg, TreeNode xts), body]) = do
  let (xts', mis) = unzip $ map takeSquare' $ zip xts [0 ..]
  return ((m, TreeNode [xt, (mArg, TreeNode xts'), body]), (m, catMaybes mis))
takeSquare t = raiseSyntaxError (fst t) "(TREE (TREE ... TREE) TREE)"

takeSquare' :: (TreePlus, Int) -> (TreePlus, Maybe Int)
takeSquare' ((m, TreeNodeSquare es), i) = ((m, TreeNode es), Just i)
takeSquare' (t, _) = (t, Nothing)

prefixFunName :: TreePlus -> WithEnv TreePlus
prefixFunName (m, TreeNode [xt, xts, body]) = do
  xt' <- prefixIdentPlus xt
  return (m, TreeNode [xt', xts, body])
prefixFunName t = raiseSyntaxError (fst t) "(TREE TREE TREE)"

prefixIdentPlus :: TreePlus -> WithEnv TreePlus
prefixIdentPlus (m, TreeLeaf x) = do
  x' <- withSectionPrefix x
  return (m, TreeLeaf x')
prefixIdentPlus (m, TreeNode [(mx, TreeLeaf x), t]) = do
  x' <- withSectionPrefix x
  return (m, TreeNode [(mx, TreeLeaf x'), t])
prefixIdentPlus t = raiseSyntaxError (fst t) "LEAF | (LEAF TREE)"

extractFunName :: TreePlus -> WithEnv Identifier
extractFunName (_, TreeNode ((_, TreeLeaf x):_)) = return $ asIdent x
extractFunName (_, TreeNode ((_, TreeNode [(_, TreeLeaf x), _]):_)) =
  return $ asIdent x
extractFunName t = raiseSyntaxError (fst t) "(LEAF ...) | ((LEAF TREE) ...)"

parseStmtClause :: TreePlus -> WithEnv (T.Text, [TreePlus])
parseStmtClause (_, TreeNode ((_, TreeLeaf x):stmtList)) = return (x, stmtList)
parseStmtClause (m, _) = raiseSyntaxError m "(LEAF TREE*)"

retrieveCompileTimeVarValue :: Meta -> T.Text -> WithEnv T.Text
retrieveCompileTimeVarValue _ "OS" = showOS <$> getOS
retrieveCompileTimeVarValue _ "architecture" = showArch <$> getArch
retrieveCompileTimeVarValue m var =
  raiseError m $ "no such compile-time variable defined: " <> var

isSpecialForm :: TreePlus -> Bool
isSpecialForm (_, TreeNode ((_, TreeLeaf x):_)) = S.member x keywordSet
isSpecialForm _ = False

keywordSet :: S.Set T.Text
keywordSet =
  S.fromList
    [ "notation"
    , "keyword"
    , "enum"
    , "include"
    , "ensure"
    , "constant"
    , "use"
    , "unuse"
    , "section"
    , "end"
    , "statement"
    , "attribute"
    , "introspect"
    , "let"
    , "definition"
    , "inductive"
    , "coinductive"
    ]

concatQuasiStmtList :: [QuasiStmt] -> WithEnv WeakStmt
concatQuasiStmtList [] = do
  path <- getCurrentFilePath
  content <- liftIO $ TIO.readFile $ toFilePath path
  let m = newMeta (length $ T.lines content) 1 path
  return $ WeakStmtReturn (m, WeakTermEnumIntro $ EnumValueIntS 64 0)
concatQuasiStmtList [QuasiStmtLet _ _ e]
  -- path <- getCurrentFilePath
  -- content <- liftIO $ TIO.readFile $ toFilePath path
  -- let m = newMeta (length $ T.lines content) 1 path
 = do
  return $ WeakStmtReturn e
concatQuasiStmtList (QuasiStmtConstDecl m xt:es) = do
  cont <- concatQuasiStmtList es
  return $ WeakStmtConstDecl m xt cont
concatQuasiStmtList (QuasiStmtLet m xt e:es) = do
  cont <- concatQuasiStmtList es
  return $ WeakStmtLet m xt e cont
concatQuasiStmtList (QuasiStmtLetWT m xt e:es) = do
  cont <- concatQuasiStmtList es
  return $ WeakStmtLetWT m xt e cont
concatQuasiStmtList (QuasiStmtLetSigma m xts e:es) = do
  cont <- concatQuasiStmtList es
  return $ WeakStmtLetSigma m xts e cont
concatQuasiStmtList (QuasiStmtImplicit m x i:es) = do
  cont <- concatQuasiStmtList es
  return $ WeakStmtImplicit m x i cont
concatQuasiStmtList (QuasiStmtImplicitPlus m x i:es) = do
  cont <- concatQuasiStmtList es
  return $ WeakStmtImplicit m x i cont
concatQuasiStmtList (QuasiStmtEnum {}:ss) = concatQuasiStmtList ss
concatQuasiStmtList (QuasiStmtDef xds:ss) = do
  let ds = map snd xds
  let baseSub = map defToSub ds
  let sub = selfCompose (length baseSub) baseSub
  let varList = map (\(_, (m, x, _), _, _) -> (m, WeakTermUpsilon x)) ds
  let iterList = map (substWeakTermPlus sub) varList
  concatQuasiStmtList $ (toLetList $ zip xds iterList) ++ ss
concatQuasiStmtList ((QuasiStmtLetInductive n m at e):es) = do
  insForm n at e
  cont <- concatQuasiStmtList es
  return $ WeakStmtLetWT m at e cont
concatQuasiStmtList (QuasiStmtLetCoinductive n m at e:es) = do
  insForm n at e
  cont <- concatQuasiStmtList es
  return $ WeakStmtLetWT m at e cont
concatQuasiStmtList (QuasiStmtLetInductiveIntro m (bi, ai) bt xts yts ats bts bInner isub as:ss) = do
  yts' <- mapM (internalize isub (ats ++ bts)) yts
  insInductive as bt -- register the constructor (if necessary)
  cont <- concatQuasiStmtList ss
  return $
    WeakStmtLetInductiveIntro
      m
      (bi, ai)
      bt
      xts
      yts
      (ats ++ bts)
      (m, WeakTermPiElim bInner yts')
      cont
concatQuasiStmtList (QuasiStmtLetCoinductiveElim m bt xtsyt codInner ats bts yt e1 e2 csub asOuter:ss) = do
  e2' <- externalize csub (ats ++ bts) codInner e2
  insCoinductive asOuter bt -- register the destructor (if necessary)
  cont <- concatQuasiStmtList ss
  let codOuter = substWeakTermPlus csub codInner
  return $
    WeakStmtLetWT
      m
      bt
      ( m
      , WeakTermPiIntro
          xtsyt
          (m, WeakTermSigmaElim codOuter (ats ++ bts ++ [yt]) e1 e2'))
      cont
concatQuasiStmtList (QuasiStmtUse _:ss) = concatQuasiStmtList ss
concatQuasiStmtList (QuasiStmtUnuse _:ss) = concatQuasiStmtList ss

toLetList :: [(IdentDef, WeakTermPlus)] -> [QuasiStmt]
toLetList [] = []
toLetList (((x, (m, (mx, _, t), _, _)), iter):rest) =
  QuasiStmtLet m (mx, x, t) iter : toLetList rest

defToSub :: Def -> (Identifier, WeakTermPlus)
defToSub (m, (mx, x, t), xts, e) = (x, (m, WeakTermIter (mx, x, t) xts e))

selfCompose :: Int -> SubstWeakTerm -> SubstWeakTerm
selfCompose 0 sub = sub
selfCompose n sub = compose sub $ selfCompose (n - 1) sub

compose :: SubstWeakTerm -> SubstWeakTerm -> SubstWeakTerm
compose s1 s2 = do
  let domS2 = map fst s2
  let codS2 = map snd s2
  let codS2' = map (substWeakTermPlus s1) codS2
  let s1' = filter (\(ident, _) -> ident `notElem` domS2) s1
  s1' ++ zip domS2 codS2'

checkKeywordSanity :: Meta -> T.Text -> WithEnv ()
checkKeywordSanity m "" = raiseError m "empty string for a keyword"
checkKeywordSanity m x
  | T.last x == '+' = raiseError m "A +-suffixed name cannot be a keyword"
checkKeywordSanity _ _ = return ()

showCyclicPath :: [Path Abs File] -> T.Text
showCyclicPath [] = ""
showCyclicPath [path] = T.pack (toFilePath path)
showCyclicPath (path:ps) =
  "     " <> T.pack (toFilePath path) <> showCyclicPath' ps

showCyclicPath' :: [Path Abs File] -> T.Text
showCyclicPath' [] = ""
showCyclicPath' [path] = "\n  ~> " <> T.pack (toFilePath path)
showCyclicPath' (path:ps) =
  "\n  ~> " <> T.pack (toFilePath path) <> showCyclicPath' ps

reportCyclicPath :: Meta -> Path Abs File -> WithEnv a
reportCyclicPath m newPath = do
  tenv <- gets traceEnv
  let cyclicPath = dropWhile (/= newPath) (reverse tenv) ++ [newPath]
  raiseError m $ "found cyclic inclusion:\n" <> showCyclicPath cyclicPath

ensureFileExistence :: Meta -> Path Abs File -> WithEnv ()
ensureFileExistence m path = do
  b <- doesFileExist path
  if b
    then return ()
    else raiseError m $ "no such file: " <> T.pack (toFilePath path)

install :: L.ByteString -> Path Abs Dir -> WithEnv ()
install bytestr pkgPath = do
  liftIO $ Tar.unpack (toFilePath pkgPath) $ Tar.read $ GZip.decompress bytestr

includeCore :: Meta -> [TreePlus] -> [TreePlus]
includeCore _ ((_, TreeNode [(_, TreeLeaf "no-implicit-core")]):rest) = rest
includeCore m treeList = includeCore' m : treeList

includeCore' :: Meta -> TreePlus
includeCore' m =
  ( m
  , TreeNode
      [ (m, TreeLeaf "include")
      , (m, TreeLeaf "library")
      , (m, TreeLeaf "\"core/core.neut\"")
      ])
