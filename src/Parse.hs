{-# LANGUAGE OverloadedStrings #-}

module Parse
  ( parse
  , complete
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.List
import Data.Maybe (catMaybes)
import Data.Monoid ((<>))
import Path
import Path.IO
import Text.Read (readMaybe)

import qualified Data.HashMap.Strict as Map
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

import Data.Basic
import Data.Env
import Data.Tree
import Data.WeakTerm
import Parse.Interpret
import Parse.MacroExpand
import Parse.Rename
import Parse.Rule
import Parse.Tokenize
import Parse.Utility

parse :: Path Abs File -> WithEnv WeakStmt
parse inputPath = do
  stmtList <- visit inputPath
  stmtList' <- renameQuasiStmtList stmtList
  pushTrace inputPath
  concatQuasiStmtList stmtList'

visit :: Path Abs File -> WithEnv [QuasiStmt]
visit path = do
  pushTrace path
  modify (\env -> env {fileEnv = Map.insert path VisitInfoActive (fileEnv env)})
  modify (\env -> env {phase = 1 + phase env})
  content <- liftIO $ TIO.readFile $ toFilePath path
  tokenize content >>= parse'

leave :: WithEnv [QuasiStmt]
leave = do
  path <- getCurrentFilePath
  popTrace
  modify (\env -> env {fileEnv = Map.insert path VisitInfoFinish (fileEnv env)})
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
  case getPosInfo m of
    Nothing -> showCompInfo xms
    Just (path, (_, l, c)) -> do
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
          let info' = filter (filterCompInfo prefix) info
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
parse' ((m, TreeNode ((_, TreeLeaf "enum"):rest)):as)
  | (_, TreeLeaf name):ts <- rest = do
    xis <- interpretEnumItem m ts
    m' <- adjustPhase m
    insEnumEnv m' name xis
    parse' as
  | otherwise = raiseSyntaxError m "(enum LEAF TREE ... TREE)"
parse' ((m, TreeNode ((_, TreeLeaf "include"):rest)):as)
  | [(_, TreeLeaf pathString)] <- rest = do
    case readMaybe (T.unpack pathString) :: Maybe String of
      Nothing -> raiseError m "the argument of `include` must be a string"
      Just path -> do
        oldPath <- getCurrentFilePath
        newPath <- resolveFile (parent oldPath) path
        ensureFileExistence m newPath
        denv <- gets fileEnv
        case Map.lookup newPath denv of
          Just VisitInfoActive -> reportCyclicPath m newPath
          Just VisitInfoFinish -> parse' as
          Nothing -> do
            includedQuasiStmtList <- visit newPath
            defList <- parse' as
            return $ includedQuasiStmtList ++ defList
  | otherwise = raiseSyntaxError m "(include LEAF)"
parse' ((_, TreeNode ((_, TreeLeaf "statement"):as1)):as2) = parse' $ as1 ++ as2
parse' ((m, TreeNode ((_, TreeLeaf "select-statement"):rest)):as2)
  | ((mx, TreeLeaf x):stmtClauseList) <- rest = do
    val <- retrieveCompileTimeVarValue mx x
    stmtClauseList' <- mapM parseStmtClause stmtClauseList
    case lookup val stmtClauseList' of
      Nothing -> parse' as2
      Just as1 -> parse' $ as1 ++ as2
  | otherwise = raiseSyntaxError m "(select-statement LEAF TREE*)"
parse' ((m, TreeNode ((_, TreeLeaf "constant"):rest)):as)
  | [(mn, TreeLeaf name), t] <- rest = do
    t' <- macroExpand t >>= interpret
    cenv <- gets constantEnv
    case Map.lookup name cenv of
      Just _ -> raiseError m $ "the constant " <> name <> " is already defined"
      Nothing -> do
        i <- newCount
        modify (\e -> e {constantEnv = Map.insert name i (constantEnv e)})
        defList <- parse' as
        m' <- adjustPhase m
        mn' <- adjustPhase mn
        return $ QuasiStmtConstDecl m' (mn', I (name, i), t') : defList
  | otherwise = raiseSyntaxError m "(constant LEAF TREE)"
parse' ((m, TreeNode ((_, TreeLeaf "attribute"):rest)):as)
  | (_, TreeLeaf name):attrList <- rest = do
    ss1 <- mapM (parseAttr name) attrList
    ss2 <- parse' as
    return $ ss1 ++ ss2
  | otherwise = raiseSyntaxError m "(attribute LEAF TREE ... TREE)"
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
    stmtList1 <- parseInductive m rest
    stmtList2 <- parse' as
    return $ stmtList1 ++ stmtList2
parse' ((m, TreeNode (coind@(_, TreeLeaf "coinductive"):rest)):as)
  | name@(mFun, TreeLeaf _):xts@(_, TreeNode _):rest' <- rest = do
    parse' $ (m, TreeNode [coind, (mFun, TreeNode (name : xts : rest'))]) : as
  | otherwise = do
    stmtList1 <- parseCoinductive m rest
    stmtList2 <- parse' as
    return $ stmtList1 ++ stmtList2
parse' ((m, TreeNode ((mLet, TreeLeaf "let"):rest)):as)
  | [(mx, TreeLeaf x), t, e] <- rest = do
    let xt = (mx, TreeNode [(mx, TreeLeaf x), t])
    parse' ((m, TreeNode [(mLet, TreeLeaf "let"), xt, e]) : as)
  | [xt, e] <- rest = do
    m' <- adjustPhase m
    e' <- macroExpand e >>= interpret
    (mx, x, t) <- macroExpand xt >>= interpretIdentifierPlus
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
          name <- newNameWith'' "hole-parse-last"
          t <- newHole m
          defList <- parse' as
          let m' = m {metaIsAppropriateAsCompletionCandidate = False}
          return $ QuasiStmtLet m' (m', name, t) e' : defList

parseBorrow :: WeakTermPlus -> (Maybe (Meta, Identifier), WeakTermPlus)
parseBorrow (m, WeakTermUpsilon (I (s, _)))
  | T.length s > 1
  , T.head s == '&' =
    (Just (m, asIdent $ T.tail s), (m, WeakTermUpsilon $ asIdent $ T.tail s))
parseBorrow t = (Nothing, t)

parseAttr :: T.Text -> TreePlus -> WithEnv QuasiStmt
parseAttr name (m, TreeNode [(_, TreeLeaf "implicit"), (_, TreeLeaf num)]) = do
  case readMaybe $ T.unpack num of
    Nothing -> raiseError m "the argument of `implicit` must be an integer"
    Just i -> return $ QuasiStmtImplicit m (asIdent name) i
parseAttr _ t = raiseError (fst t) $ "invalid attribute: " <> showAsSExp t

parseDef :: [TreePlus] -> WithEnv [QuasiStmt]
parseDef xds = do
  xds' <- mapM (insImplicitBegin >=> macroExpand) xds
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

insImplicitBegin :: TreePlus -> WithEnv TreePlus
insImplicitBegin (m, TreeNode (xt:xts:body:rest)) = do
  let m' = fst body
  let beginBlock = (m', TreeNode ((m', TreeLeaf "begin") : body : rest))
  return (m, TreeNode [xt, xts, beginBlock])
insImplicitBegin t = raiseSyntaxError (fst t) "(TREE TREE TREE ...)"

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
    , "attribute"
    , "constant"
    , "statement"
    , "select-statement"
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

newHole :: Meta -> WithEnv WeakTermPlus
newHole m = do
  h <- newNameWith'' "hole-parse-zeta"
  return (m, WeakTermZeta h)

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
