{-# LANGUAGE OverloadedStrings #-}

module Parse
  ( parse
  , parse'
  , includeCore
  , pushTrace
  ) where

import Control.Monad.Except
import Control.Monad.State hiding (get)
import Data.ByteString.Builder

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

parse :: Path Abs File -> WithEnv WeakStmt
parse inputPath = do
  stmtList <- visit inputPath
  stmtList' <- discern stmtList
  warnUnusedVar
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
  modify (\env -> env {sectionEnv = []})
  return []

pushTrace :: Path Abs File -> WithEnv ()
pushTrace path = modify (\env -> env {traceEnv = path : traceEnv env})

popTrace :: WithEnv ()
popTrace = modify (\env -> env {traceEnv = tail (traceEnv env)})

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
    modify (\e -> e {sectionEnv = s : sectionEnv e})
    n <- getCurrentSection
    stmtList <- parse' as
    return $ QuasiStmtUse n : QuasiStmtUse (n <> ":" <> "private") : stmtList -- auto-use
  | otherwise = raiseSyntaxError m "(section LEAF)"
parse' ((m, TreeNode ((_, TreeLeaf "end"):es)):as)
  | [(_, TreeLeaf s)] <- es = do
    ns <- gets sectionEnv
    case ns of
      [] -> raiseError m "there is no section to end"
      (s':ns')
        | s == s' -> do
          n <- getCurrentSection
          modify (\e -> e {sectionEnv = ns'})
          stmtList <- parse' as
          return $
            QuasiStmtUnuse n : QuasiStmtUnuse (n <> ":" <> "private") : stmtList
        | otherwise ->
          raiseError m $
          "the innermost section is not `" <> s <> "`, but is `" <> s' <> "`"
  | otherwise = raiseSyntaxError m "(end LEAF)"
parse' ((m, TreeNode ((_, TreeLeaf "enum"):rest)):as)
  | (_, TreeLeaf name):ts <- rest = do
    xis <- interpretEnumItem m name ts
    m' <- adjustPhase' m
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
      note' $ "downloading " <> pkg <> " from " <> TE.decodeUtf8 urlStr'
      item <- liftIO $ get urlStr' lazyConcatHandler
      note' $ "installing " <> pkg <> " into " <> T.pack (toFilePath path)
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
    t' <- adjustPhase t >>= macroExpand >>= interpret
    name' <- withSectionPrefix name
    set <- gets constantSet
    if S.member name' set
      then raiseError m $ "the constant " <> name' <> " is already defined"
      else do
        modify (\env -> env {constantSet = S.insert name' set})
        defList <- parse' as
        m' <- adjustPhase' m
        mn' <- adjustPhase' mn
        return $ QuasiStmtConstDecl m' (mn', name', t') : defList
  | otherwise = raiseSyntaxError m "(constant LEAF TREE)"
parse' ((m, TreeNode (def@(mDef, TreeLeaf "definition"):rest)):as)
  | [name@(_, TreeLeaf _), body] <- rest =
    parse' $ (m, TreeNode [(mDef, TreeLeaf "let"), name, body]) : as
  | name@(mFun, TreeLeaf _):xts@(_, TreeNode _):body:rest' <- rest = do
    parse' $
      (m, TreeNode [def, (mFun, TreeNode (name : xts : body : rest'))]) : as
  | otherwise = do
    s <- parseDef rest
    ss <- parse' as
    return $ s : ss
parse' ((m, TreeNode (ind@(_, TreeLeaf "inductive"):rest)):as)
  | name@(mFun, TreeLeaf _):xts@(_, TreeNode _):rest' <- rest = do
    parse' $ (m, TreeNode [ind, (mFun, TreeNode (name : xts : rest'))]) : as
  | otherwise = do
    rest' <- mapM (adjustPhase >=> macroExpand) rest
    m' <- adjustPhase' m
    stmtList1 <- parseInductive m' rest'
    stmtList2 <- parse' as
    return $ stmtList1 ++ stmtList2
parse' ((m, TreeNode (coind@(_, TreeLeaf "coinductive"):rest)):as)
  | name@(mFun, TreeLeaf _):xts@(_, TreeNode _):rest' <- rest = do
    parse' $ (m, TreeNode [coind, (mFun, TreeNode (name : xts : rest'))]) : as
  | otherwise = do
    rest' <- mapM (adjustPhase >=> macroExpand) rest
    registerLabelInfo rest'
    rest'' <- asInductive rest'
    stmtList1 <- parseInductive m rest''
    stmtList2 <- generateProjections rest'
    stmtList3 <- parse' as
    return $ stmtList1 ++ stmtList2 ++ stmtList3
parse' ((m, TreeNode ((mLet, TreeLeaf "let"):rest)):as)
  | [(mx, TreeLeaf x), t, e] <- rest = do
    let xt = (mx, TreeNode [(mx, TreeLeaf x), t])
    parse' ((m, TreeNode [(mLet, TreeLeaf "let"), xt, e]) : as)
  | [xt, e] <- rest = do
    m' <- adjustPhase' m
    e' <- adjustPhase e >>= macroExpand >>= interpret
    xt' <-
      adjustPhase xt >>= macroExpand >>= prefixTextPlus >>= interpretTextPlus
    defList <- parse' as
    return $ QuasiStmtLet m' xt' e' : defList
  | otherwise = raiseSyntaxError m "(let LEAF TREE TREE) | (let TREE TREE)"
parse' ((m, TreeNode ((_, TreeLeaf "verify"):rest)):as)
  | [e] <- rest = do
    e' <- adjustPhase e >>= macroExpand >>= interpret
    m' <- adjustPhase' m
    defList <- parse' as
    return $ QuasiStmtVerify m' e' : defList
  | otherwise = raiseSyntaxError m "(include LEAF) | (include library LEAF)"
parse' (a:as) = do
  e <- adjustPhase a >>= macroExpand
  if isSpecialForm e
    then parse' $ e : as
    else do
      e' <- interpret e
      name <- newTextWith "_"
      m' <- adjustPhase' $ metaOf e'
      t <- newHole m'
      defList <- parse' as
      return $ QuasiStmtLet m' (m', name, t) e' : defList

lazyConcatHandler :: Response -> InputStream B.ByteString -> IO L.ByteString
lazyConcatHandler _ i1 = do
  i2 <- Streams.map byteString i1
  x <- Streams.fold mappend mempty i2
  return $ toLazyByteString x

withSectionPrefix :: T.Text -> WithEnv T.Text
withSectionPrefix x = do
  ns <- gets sectionEnv
  return $ withSectionPrefix' ns x

withSectionPrefix' :: [T.Text] -> T.Text -> T.Text
withSectionPrefix' [] x = x
withSectionPrefix' (n:ns) x = withSectionPrefix' ns $ n <> ":" <> x

getCurrentSection :: WithEnv T.Text
getCurrentSection = do
  ns <- gets sectionEnv
  return $ getCurrentSection' ns

getCurrentSection' :: [T.Text] -> T.Text
getCurrentSection' [] = ""
getCurrentSection' [n] = n
getCurrentSection' (n:ns) = getCurrentSection' ns <> ":" <> n

asInductive :: [TreePlus] -> WithEnv [TreePlus]
asInductive [] = return []
asInductive (t:ts) = do
  (sub, t') <- asInductive' t
  ts' <- asInductive $ map (substTree sub) ts
  return $ t' : ts'

asInductive' :: TreePlus -> WithEnv ((T.Text, T.Text), TreePlus)
asInductive' (m, TreeNode ((_, TreeLeaf a):(_, TreeNode xts):rules)) = do
  let a' = "(" <> a <> ")"
  let sub = (a, a')
  let xts' = map (substTree sub) xts
  rules'' <- mapM styleRule $ map (substTree sub) rules
  let hole = "(_)"
  argList <- mapM extractArg xts
  return
    ( (a, a')
    , ( m
      , TreeNode
          [ (m, TreeLeaf a)
          , (m, TreeNode xts')
          , ( m
            , TreeNode
                [ (m, TreeLeaf "unfold")
                , ( m
                  , TreeNode
                      ([ ( m
                         , TreeNode
                             [ (m, TreeLeaf a')
                             , ( m
                               , TreeNode
                                   [ (m, TreeLeaf "pi")
                                   , (m, TreeNode xts')
                                   , (m, TreeLeaf "tau")
                                   ])
                             ])
                       ] ++
                       rules'' ++
                       [ ( m
                         , TreeNode
                             [ (m, TreeLeaf hole)
                             , (m, TreeNode ((m, TreeLeaf a') : argList))
                             ])
                       ]))
                , (m, TreeNode ((m, TreeLeaf a) : argList))
                ])
          ]))
asInductive' t = raiseSyntaxError (fst t) "(LEAF (TREE ... TREE) ...)"

extractArg :: TreePlus -> WithEnv TreePlus
extractArg (m, TreeLeaf x) = return (m, TreeLeaf x)
extractArg (_, TreeNode [(m, TreeLeaf x), _]) = return (m, TreeLeaf x)
extractArg t = raiseSyntaxError (fst t) "LEAF | (LEAF TREE)"

styleRule :: TreePlus -> WithEnv TreePlus
styleRule (m, TreeNode [(mName, TreeLeaf name), (_, TreeNode xts), t]) = do
  return
    ( m
    , TreeNode
        [ (mName, TreeLeaf name)
        , (m, TreeNode [(m, TreeLeaf "pi"), (m, TreeNode xts), t])
        ])
styleRule t = raiseSyntaxError (fst t) "(LEAF (TREE ... TREE) TREE)"

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
parseAttr name (m, TreeNode ((_, TreeLeaf "implicit"):rest))
  | Just mxs <- mapM asLeaf rest = do
    case mapM (readMaybe . T.unpack . snd) mxs of
      Nothing -> raiseError m "the argument of `implicit` must be an integer"
      Just is -> return $ QuasiStmtImplicit m name is
parseAttr _ t = raiseSyntaxError (fst t) "(implicit LEAF ... LEAF)"

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
  ns <- gets sectionEnv
  penv <- gets prefixEnv
  case (null ns, null penv) of
    (False, _) -> raiseError m "`include` can only be used at top-level section"
    (_, False) ->
      raiseError m "`include` can only be used with no prefix assumption"
    _ -> return ()

parseDef :: [TreePlus] -> WithEnv QuasiStmt
parseDef xds = do
  xds' <- mapM (adjustPhase >=> prefixFunName >=> macroExpand) xds
  xs <- mapM extractFunName xds'
  xds'' <- mapM interpretIter xds'
  return $ QuasiStmtDef (zip xs xds'')

prefixFunName :: TreePlus -> WithEnv TreePlus
prefixFunName (m, TreeNode [xt, xts, body]) = do
  xt' <- prefixTextPlus xt
  return (m, TreeNode [xt', xts, body])
prefixFunName t = raiseSyntaxError (fst t) "(TREE TREE TREE)"

prefixTextPlus :: TreePlus -> WithEnv TreePlus
prefixTextPlus (m, TreeLeaf "_") = return (m, TreeLeaf "_")
prefixTextPlus (m, TreeLeaf x) = do
  x' <- withSectionPrefix x
  return (m, TreeLeaf x')
prefixTextPlus (m, TreeNode [(mx, TreeLeaf "_"), t]) =
  return (m, TreeNode [(mx, TreeLeaf "_"), t])
prefixTextPlus (m, TreeNode [(mx, TreeLeaf x), t]) = do
  x' <- withSectionPrefix x
  return (m, TreeNode [(mx, TreeLeaf x'), t])
prefixTextPlus t = raiseSyntaxError (fst t) "LEAF | (LEAF TREE)"

extractFunName :: TreePlus -> WithEnv T.Text
extractFunName (_, TreeNode ((_, TreeLeaf x):_)) = return x
extractFunName (_, TreeNode ((_, TreeNode [(_, TreeLeaf x), _]):_)) = return x
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
concatQuasiStmtList (QuasiStmtConstDecl m xt:es) = do
  cont <- concatQuasiStmtList es
  return $ WeakStmtConstDecl m xt cont
concatQuasiStmtList (QuasiStmtLet m xt e:es) = do
  cont <- concatQuasiStmtList es
  return $ WeakStmtLet m xt e cont
concatQuasiStmtList (QuasiStmtLetWT m xt e:es) = do
  cont <- concatQuasiStmtList es
  return $ WeakStmtLetWT m xt e cont
concatQuasiStmtList (QuasiStmtVerify m e:es) = do
  cont <- concatQuasiStmtList es
  return $ WeakStmtVerify m e cont
concatQuasiStmtList (QuasiStmtImplicit m x i:es) = do
  cont <- concatQuasiStmtList es
  return $ WeakStmtImplicit m x i cont
concatQuasiStmtList (QuasiStmtEnum {}:ss) = concatQuasiStmtList ss
concatQuasiStmtList (QuasiStmtDef xds:ss) = do
  let ds = map snd xds
  let baseSub = Map.fromList $ map defToSub ds
  let sub = selfCompose (length baseSub) baseSub
  let varList = map (\(_, (m, x, _), _, _) -> (m, WeakTermUpsilon x)) ds
  let iterList = map (substWeakTermPlus sub) varList
  concatQuasiStmtList $ (toLetList $ zip xds iterList) ++ ss
concatQuasiStmtList ((QuasiStmtLetInductive n m at e):es) = do
  insForm n at e
  cont <- concatQuasiStmtList es
  return $ WeakStmtLetWT m at e cont
concatQuasiStmtList (QuasiStmtLetInductiveIntro m bt e as:ss) = do
  case e of
    (mLam, WeakTermPiIntro xtsyts (_, WeakTermPiIntroPlus (bi, _) atsbts (_, WeakTermPiElim b _))) -> do
      (_, is) <- lookupRevIndEnv m bi
      yts' <- mapM (internalize as atsbts) $ drop (length (is :: [Int])) xtsyts
      insInductive as bt -- register the constructor (if necessary)
      cont <- concatQuasiStmtList ss
      return $
        WeakStmtLetWT
          m
          bt
          ( mLam -- metaIsReducible mLam == False
          , WeakTermPiIntro
              xtsyts
              ( m
              , WeakTermPiIntroPlus
                  (bi, xtsyts)
                  atsbts
                  (m, WeakTermPiElim b yts')))
          cont
    _ -> raiseCritical m "inductive-intro"
concatQuasiStmtList (QuasiStmtUse _:ss) = concatQuasiStmtList ss
concatQuasiStmtList (QuasiStmtUnuse _:ss) = concatQuasiStmtList ss

toLetList :: [(IdentDef, WeakTermPlus)] -> [QuasiStmt]
toLetList [] = []
toLetList (((x, (m, (mx, _, t), _, _)), iter):rest) =
  QuasiStmtLet m (mx, x, t) iter : toLetList rest

defToSub :: Def -> (Key, WeakTermPlus)
defToSub (m, (mx, x, t), xts, e) =
  (Left $ asInt x, (m, WeakTermIter (mx, x, t) xts e))

selfCompose :: Int -> SubstWeakTerm -> SubstWeakTerm
selfCompose 0 sub = sub
selfCompose n sub = compose sub $ selfCompose (n - 1) sub

compose :: SubstWeakTerm -> SubstWeakTerm -> SubstWeakTerm
compose s1 s2 = do
  Map.union (Map.map (substWeakTermPlus s1) s2) s1
  -- IntMap.union s1 $ IntMap.map (substWeakTermPlus s1) s2
  -- let domS2 = map fst s2
  -- let codS2 = map snd s2
  -- let codS2' = map (substWeakTermPlus s1) codS2
  -- let s1' = filter (\(ident, _) -> ident `notElem` domS2) s1
  -- s1' ++ zip domS2 codS2'

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

adjustPhase :: TreePlus -> WithEnv TreePlus
adjustPhase (m, TreeLeaf x) = do
  m' <- adjustPhase' m
  return (m', TreeLeaf x)
adjustPhase (m, TreeNode ts) = do
  m' <- adjustPhase' m
  ts' <- mapM adjustPhase ts
  return (m', TreeNode ts')

adjustPhase' :: Meta -> WithEnv Meta
adjustPhase' m = do
  i <- gets phase
  let (_, l, c) = metaLocation m
  return $ m {metaLocation = (i, l, c)}

warnUnusedVar :: WithEnv ()
warnUnusedVar =
  whenCheck $ do
    set <- gets intactSet
    let set' = S.map (\(m, x) -> (getPosInfo m, x)) set
    warnUnusedVar' $ S.toList set'

warnUnusedVar' :: [(PosInfo, T.Text)] -> WithEnv ()
warnUnusedVar' [] = return ()
warnUnusedVar' ((pos, x):pxs)
  | T.all (`S.notMember` S.fromList "()") x = do
    warn pos $ "defined but not used: `" <> x <> "`"
    warnUnusedVar' pxs
  | otherwise = warnUnusedVar' pxs
