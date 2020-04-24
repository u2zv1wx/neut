module Parse
  ( parse,
    parse',
    includeCore,
    pushTrace,
  )
where

import qualified Codec.Archive.Tar as Tar
import qualified Codec.Compression.GZip as GZip
import Control.Monad.State.Lazy hiding (get)
import Data.Basic
import Data.ByteString.Builder
import qualified Data.ByteString.Lazy as L
import Data.Env
import qualified Data.HashMap.Lazy as Map
import qualified Data.IntMap as IntMap
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import Data.Tree
import Data.WeakTerm
import Network.Http.Client
import Parse.Discern
import Parse.Interpret
import Parse.MacroExpand
import Parse.Rule
import Parse.Tokenize
import Path
import Path.IO
import qualified System.IO.Streams as Streams
import Text.Read (readMaybe)

parse :: Path Abs File -> WithEnv [WeakStmt]
parse inputPath = do
  stmtList <- visit inputPath
  pushTrace inputPath
  return stmtList

visit :: Path Abs File -> WithEnv [WeakStmt]
visit path = do
  pushTrace path
  modify (\env -> env {fileEnv = Map.insert path VisitInfoActive (fileEnv env)})
  modify (\env -> env {phase = 1 + phase env})
  content <- liftIO $ TIO.readFile $ toFilePath path
  treeList <- tokenize content
  parse' $ includeCore (newMeta 1 1 path) treeList

leave :: WithEnv [WeakStmt]
leave = do
  path <- getCurrentFilePath
  popTrace
  modify (\env -> env {fileEnv = Map.insert path VisitInfoFinish (fileEnv env)})
  modify (\env -> env {prefixEnv = []})
  modify (\env -> env {sectionEnv = []})
  return []

pushTrace :: Path Abs File -> WithEnv ()
pushTrace path =
  modify (\env -> env {traceEnv = path : traceEnv env})

popTrace :: WithEnv ()
popTrace =
  modify (\env -> env {traceEnv = tail (traceEnv env)})

parse' :: [TreePlus] -> WithEnv [WeakStmt]
parse' stmtTreeList =
  case stmtTreeList of
    [] -> leave
    (headStmt : restStmtList) ->
      case headStmt of
        (m, TreeNode (leaf@(_, TreeLeaf headAtom) : rest)) ->
          case headAtom of
            "attribute"
              | (mx, TreeLeaf x) : attrList <- rest -> do
                impList <- mapM (parseAttr mx x) attrList
                cont <- parse' restStmtList
                return $ impList ++ cont
              | otherwise ->
                raiseSyntaxError m "(attribute LEAF TREE ... TREE)"
            "notation"
              | [from, to] <- rest -> do
                checkNotationSanity from
                modify (\e -> e {notationEnv = (from, to) : notationEnv e})
                parse' restStmtList
              | otherwise -> raiseSyntaxError m "(notation TREE TREE)"
            "keyword"
              | [(_, TreeLeaf s)] <- rest -> do
                checkKeywordSanity m s
                modify (\e -> e {keywordEnv = S.insert s (keywordEnv e)})
                parse' restStmtList
              | otherwise -> raiseSyntaxError m "(keyword LEAF)"
            "use"
              | [(_, TreeLeaf s)] <- rest ->
                use s >> parse' restStmtList
              | otherwise -> raiseSyntaxError m "(use LEAF)"
            "unuse"
              | [(_, TreeLeaf s)] <- rest ->
                unuse s >> parse' restStmtList
              | otherwise -> raiseSyntaxError m "(unuse LEAF)"
            "section"
              | [(_, TreeLeaf s)] <- rest -> do
                modify (\e -> e {sectionEnv = s : sectionEnv e})
                getCurrentSection >>= use
                parse' restStmtList
              | otherwise -> raiseSyntaxError m "(section LEAF)"
            "end"
              | [(_, TreeLeaf s)] <- rest -> do
                ns <- gets sectionEnv
                case ns of
                  [] -> raiseError m "there is no section to end"
                  (s' : ns')
                    | s == s' -> do
                      getCurrentSection >>= unuse
                      modify (\e -> e {sectionEnv = ns'})
                      parse' restStmtList
                    | otherwise ->
                      raiseError m $
                        "the innermost section is not `" <> s <> "`, but is `" <> s' <> "`"
              | otherwise -> raiseSyntaxError m "(end LEAF)"
            "enum"
              | (_, TreeLeaf name) : ts <- rest -> do
                m' <- adjustPhase' m
                xis <- interpretEnumItem m' name ts
                insEnumEnv m' name xis
                parse' restStmtList
              | otherwise -> raiseSyntaxError m "(enum LEAF TREE ... TREE)"
            "include"
              | [(mPath, TreeLeaf pathString)] <- rest ->
                includeFile m mPath pathString getCurrentDirPath restStmtList
              | [(_, TreeLeaf "library"), (mPath, TreeLeaf pathString)] <- rest ->
                includeFile m mPath pathString getLibraryDirPath restStmtList
              | otherwise -> raiseSyntaxError m "(include LEAF) | (include library LEAF)"
            "ensure"
              | [(_, TreeLeaf pkg), (mUrl, TreeLeaf urlStr)] <- rest -> do
                libDir <- getLibraryDirPath
                pkg' <- parseRelDir $ T.unpack pkg
                let path = libDir </> pkg'
                isAlreadyInstalled <- doesDirExist path
                when (not isAlreadyInstalled) $ do
                  urlStr' <- readStrOrThrow mUrl urlStr
                  note' $ "downloading " <> pkg <> " from " <> TE.decodeUtf8 urlStr'
                  item <- liftIO $ get urlStr' $ \_ i1 -> do
                    i2 <- Streams.map byteString i1
                    toLazyByteString <$> Streams.fold mappend mempty i2
                  note' $ "extracting " <> pkg <> " into " <> T.pack (toFilePath path)
                  extract item path
                parse' restStmtList
              | otherwise -> raiseSyntaxError m "(ensure LEAF LEAF)"
            "statement" ->
              parse' $ rest ++ restStmtList
            "introspect"
              | ((mx, TreeLeaf x) : stmtClauseList) <- rest -> do
                val <- retrieveCompileTimeVarValue mx x
                stmtClauseList' <- mapM parseStmtClause stmtClauseList
                case lookup val stmtClauseList' of
                  Nothing -> parse' restStmtList
                  Just as1 -> parse' $ as1 ++ restStmtList
              | otherwise -> raiseSyntaxError m "(introspect LEAF TREE*)"
            "constant"
              | [(_, TreeLeaf name), t] <- rest -> do
                t' <- adjustPhase t >>= macroExpand >>= interpret >>= discern
                m' <- adjustPhase' m
                name' <- withSectionPrefix name
                insertConstant m' name'
                defList <- parse' restStmtList
                return $ WeakStmtConstDecl (m', name', t') : defList
              | otherwise -> raiseSyntaxError m "(constant LEAF TREE)"
            "define"
              | [name@(_, TreeLeaf _), body] <- rest ->
                parse' $ (m, TreeNode [(m, TreeLeaf "let"), name, body]) : restStmtList
              | name@(mFun, TreeLeaf _) : xts@(_, TreeNode _) : body : rest' <- rest ->
                parse' $ (m, TreeNode [leaf, (mFun, TreeNode (name : xts : body : rest'))]) : restStmtList
              | otherwise -> do
                ss1 <- parseDef rest
                ss2 <- parse' restStmtList
                return $ ss1 ++ ss2
            "inductive"
              | name@(mFun, TreeLeaf _) : xts@(_, TreeNode _) : es' <- rest ->
                parse' $ (m, TreeNode [leaf, (mFun, TreeNode (name : xts : es'))]) : restStmtList
              | otherwise -> do
                rest' <- mapM (adjustPhase >=> macroExpand) rest
                m' <- adjustPhase' m
                stmtList1 <- parseInductive m' rest'
                stmtList2 <- parse' restStmtList
                return $ stmtList1 ++ stmtList2
            "coinductive"
              | name@(mFun, TreeLeaf _) : xts@(_, TreeNode _) : rest' <- rest ->
                parse' $ (m, TreeNode [leaf, (mFun, TreeNode (name : xts : rest'))]) : restStmtList
              | otherwise -> do
                rest' <- mapM (adjustPhase >=> macroExpand) rest
                registerLabelInfo rest'
                rest'' <- asInductive rest'
                stmtList1 <- parseInductive m rest''
                stmtList2 <- generateProjections rest'
                stmtList3 <- parse' restStmtList
                return $ stmtList1 ++ stmtList2 ++ stmtList3
            "let"
              | [(mx, TreeLeaf x), t, e] <- rest -> do
                let xt = (mx, TreeNode [(mx, TreeLeaf x), t])
                parse' ((m, TreeNode [(m, TreeLeaf "let"), xt, e]) : restStmtList)
              | [xt, e] <- rest -> do
                m' <- adjustPhase' m
                e' <- adjustPhase e >>= macroExpand >>= interpret >>= discern
                xt' <- adjustPhase xt >>= macroExpand >>= prefixTextPlus >>= interpretIdentPlus >>= discernIdentPlus
                defList <- parse' restStmtList
                return $ WeakStmtLet m' xt' e' : defList
              | otherwise -> raiseSyntaxError m "(let LEAF TREE TREE) | (let TREE TREE)"
            "verify"
              | [e] <- rest -> do
                e' <- adjustPhase e >>= macroExpand >>= interpret >>= discern
                m' <- adjustPhase' m
                defList <- parse' restStmtList
                return $ WeakStmtVerify m' e' : defList
              | otherwise -> raiseSyntaxError m "(verify LEAF) | (verify library LEAF)"
            _ -> interpretAux headStmt restStmtList
        _ -> interpretAux headStmt restStmtList

interpretAux :: TreePlus -> [TreePlus] -> WithEnv [WeakStmt]
interpretAux headStmt restStmtList = do
  headStmt' <- adjustPhase headStmt >>= macroExpand
  if isSpecialForm headStmt'
    then parse' $ headStmt' : restStmtList
    else do
      e <- interpret headStmt' >>= discern
      h <- newNameWith'' "_"
      m' <- adjustPhase' $ metaOf e
      t <- newHole m'
      defList <- parse' restStmtList
      return $ WeakStmtLet m' (m', h, t) e : defList

use :: T.Text -> WithEnv ()
use s =
  modify (\e -> e {prefixEnv = s : prefixEnv e})

unuse :: T.Text -> WithEnv ()
unuse s =
  modify (\e -> e {prefixEnv = filter (/= s) (prefixEnv e)})

parseAttr :: Meta -> T.Text -> TreePlus -> WithEnv WeakStmt
parseAttr mx x tree =
  case tree of
    (m, TreeNode ((_, TreeLeaf headAtom) : rest)) ->
      case headAtom of
        "implicit"
          | Just mxs <- mapM asLeaf rest ->
            case mapM (readMaybe . T.unpack . snd) mxs of
              Nothing ->
                raiseError m "the argument of `implicit` must be an integer"
              Just is ->
                toStmtImplicit mx x is
          | otherwise ->
            raiseSyntaxError (fst tree) "(implicit LEAF ... LEAF)"
        _ ->
          raiseError m $ "unknown attribute: " <> headAtom
    _ ->
      raiseSyntaxError (fst tree) "(LEAF TREE ... LEAF)"

withSectionPrefix :: T.Text -> WithEnv T.Text
withSectionPrefix x = do
  ns <- gets sectionEnv
  return $ foldl (\acc n -> n <> ":" <> acc) x ns

getCurrentSection :: WithEnv T.Text
getCurrentSection = do
  ns <- gets sectionEnv
  return $ getCurrentSection' ns

getCurrentSection' :: [T.Text] -> T.Text
getCurrentSection' nameStack =
  case nameStack of
    [] ->
      ""
    [n] ->
      n
    (n : ns) ->
      getCurrentSection' ns <> ":" <> n

readStrOrThrow :: (Read a) => Meta -> T.Text -> WithEnv a
readStrOrThrow m quotedStr =
  case readMaybe (T.unpack quotedStr) of
    Nothing ->
      raiseError m "the atom here must be a string"
    Just str ->
      return str

includeFile ::
  Meta ->
  Meta ->
  T.Text ->
  WithEnv (Path Abs Dir) ->
  [TreePlus] ->
  WithEnv [WeakStmt]
includeFile m mPath pathString computeDirPath as = do
  m' <- adjustPhase' m
  mPath' <- adjustPhase' mPath
  ensureEnvSanity m'
  path <- readStrOrThrow mPath' pathString
  dirPath <- computeDirPath
  newPath <- resolveFile dirPath path
  ensureFileExistence m' newPath
  denv <- gets fileEnv
  case Map.lookup newPath denv of
    Just VisitInfoActive -> do
      tenv <- gets traceEnv
      let cyclicPath = dropWhile (/= newPath) (reverse tenv) ++ [newPath]
      raiseError m' $ "found cyclic inclusion:\n" <> showCyclicPath cyclicPath
    Just VisitInfoFinish ->
      parse' as
    Nothing -> do
      includedWeakStmtList <- visit newPath
      defList <- parse' as
      return $ includedWeakStmtList ++ defList

ensureEnvSanity :: Meta -> WithEnv ()
ensureEnvSanity m = do
  ns <- gets sectionEnv
  penv <- gets prefixEnv
  case (null ns, null penv) of
    (False, _) ->
      raiseError m "`include` can only be used at top-level section"
    (_, False) ->
      raiseError m "`include` can only be used with no prefix assumption"
    _ ->
      return ()

-- basic idea:
--   sub = {
--     x1 := μ x1. e1,
--     x2 := μ x2. e2,
--     x3 := μ x3. e3
--   }
--   sub^2 = {
--     x1 := μ x1. e1 {x2 := μ x2. e2, x3 := μ x3. e3}
--     x2 := μ x2. e2 {x3 := μ x3. e3, x1 := μ x1. e1}
--     x3 := μ x3. e3 {x1 := μ x1. e1, x2 := μ x2. e2}
--   }
--   sub^3 = {
--     x1 := μ x1. e1 {x2 := μ x2. e2 {x3 := ...}, x3 := μ x3. e3 {x2 := ...}} (closed w.r.t. x1, x2, x3)
--     x2 := μ x2. e2 {x3 := μ x3. e3 {x1 := ...}, x1 := μ x1. e1 {x2 := ...}} (closed w.r.t. x1, x2, x3)
--     x3 := μ x3. e3 {x1 := μ x1. e1 {x2 := ...}, x2 := μ x2. e2 {x1 := ...}} (closed w.r.t. x1, x2, x3)
--   }
parseDef :: [TreePlus] -> WithEnv [WeakStmt]
parseDef xds = do
  defList <- mapM (adjustPhase >=> prefixFunName >=> macroExpand) xds
  -- {f1 := def-1, ..., fn := def-n}から{f1, ..., fn}を取り出してトップレベルでdiscernする
  -- metaNameList <- mapM extractFunName defList
  metaNameList <- mapM (extractFunName >=> uncurry discernIdent) defList
  let nameList = map snd metaNameList
  -- xiの名前をtopNameEnvに追加した状態でそれぞれの定義をdiscernする
  -- defList' <- mapM interpretIter defList
  defList' <- mapM (interpretIter >=> discernDef) defList
  -- sub^nを計算する
  let baseSub = IntMap.fromList $ map defToSub $ zip nameList defList'
  -- sub^1からスタートだから、sub^nを得るためにはn - 1回追加で合成すればいい
  let sub = selfCompose (length baseSub - 1) baseSub
  -- 変数を「閉じる」
  let iterSelfVarList = map (uncurry toVar . defToName) defList'
  let aligner = IntMap.fromList $ zip (map asInt nameList) iterSelfVarList
  -- sub^nをf1, ..., fnに適用する
  let closedSub = IntMap.map (substWeakTermPlus aligner) sub -- capturing substitution
  let typeList = map (\(_, (m, _, t), _, _) -> (m, t)) defList'
  let bodyList = map (substWeakTermPlus closedSub . uncurry toVar) metaNameList
  toLetList $ zip3 nameList typeList bodyList

defToName :: Def -> (Meta, Ident)
defToName (_, (m, x, _), _, _) = (m, x)

prefixFunName :: TreePlus -> WithEnv TreePlus
prefixFunName tree =
  case tree of
    (m, TreeNode [xt, xts, body]) -> do
      xt' <- prefixTextPlus xt
      return (m, TreeNode [xt', xts, body])
    t ->
      raiseSyntaxError (fst t) "(TREE TREE TREE)"

prefixTextPlus :: TreePlus -> WithEnv TreePlus
prefixTextPlus tree =
  case tree of
    (m, TreeLeaf "_") -> do
      h <- newTextWith "_"
      return (m, TreeLeaf h)
    (m, TreeLeaf x) -> do
      x' <- withSectionPrefix x
      return (m, TreeLeaf x')
    (m, TreeNode [(mx, TreeLeaf "_"), t]) ->
      return (m, TreeNode [(mx, TreeLeaf "_"), t])
    (m, TreeNode [(mx, TreeLeaf x), t]) -> do
      x' <- withSectionPrefix x
      return (m, TreeNode [(mx, TreeLeaf x'), t])
    t ->
      raiseSyntaxError (fst t) "LEAF | (LEAF TREE)"

extractFunName :: TreePlus -> WithEnv (Meta, Ident)
extractFunName tree =
  case tree of
    (_, TreeNode ((m, TreeLeaf x) : _)) ->
      return (m, asIdent x)
    (_, TreeNode ((_, TreeNode [(m, TreeLeaf x), _]) : _)) ->
      return (m, asIdent x)
    t ->
      raiseSyntaxError (fst t) "(LEAF ...) | ((LEAF TREE) ...)"

toLetList :: [(Ident, (Meta, WeakTermPlus), WeakTermPlus)] -> WithEnv [WeakStmt]
toLetList defList =
  case defList of
    [] ->
      return []
    ((x, (m, t), e) : rest) -> do
      rest' <- toLetList rest
      return $ WeakStmtLet m (m, x, t) e : rest'

defToSub :: (Ident, Def) -> (Int, WeakTermPlus)
defToSub (dom, (m, xt, xts, e)) =
  (asInt dom, (m, WeakTermIter xt xts e))

selfCompose :: Int -> SubstWeakTerm -> SubstWeakTerm
selfCompose i sub =
  if i == 0
    then sub
    else compose sub $ selfCompose (i - 1) sub

compose :: SubstWeakTerm -> SubstWeakTerm -> SubstWeakTerm
compose s1 s2 =
  IntMap.union (IntMap.map (substWeakTermPlus s1) s2) s1

parseStmtClause :: TreePlus -> WithEnv (T.Text, [TreePlus])
parseStmtClause tree =
  case tree of
    (_, TreeNode ((_, TreeLeaf x) : stmtList)) ->
      return (x, stmtList)
    (m, _) ->
      raiseSyntaxError m "(LEAF TREE*)"

retrieveCompileTimeVarValue :: Meta -> T.Text -> WithEnv T.Text
retrieveCompileTimeVarValue m var =
  case var of
    "OS" ->
      showOS <$> getOS
    "architecture" ->
      showArch <$> getArch
    _ ->
      raiseError m $ "no such compile-time variable defined: " <> var

isSpecialForm :: TreePlus -> Bool
isSpecialForm tree =
  case tree of
    (_, TreeNode ((_, TreeLeaf x) : _)) ->
      S.member x keywordSet
    _ ->
      False

keywordSet :: S.Set T.Text
keywordSet =
  S.fromList
    [ "attribute",
      "coinductive",
      "constant",
      "define",
      "end",
      "ensure",
      "enum",
      "include",
      "inductive",
      "introspect",
      "keyword",
      "let",
      "notation",
      "section",
      "statement",
      "unuse",
      "use"
    ]

checkKeywordSanity :: Meta -> T.Text -> WithEnv ()
checkKeywordSanity m x
  | x == "" =
    raiseError m "empty string for a keyword"
  | T.last x == '+' =
    raiseError m "A +-suffixed name cannot be a keyword"
  | otherwise =
    return ()

showCyclicPath :: [Path Abs File] -> T.Text
showCyclicPath pathList =
  case pathList of
    [] ->
      ""
    [path] ->
      T.pack (toFilePath path)
    (path : ps) ->
      "     " <> T.pack (toFilePath path) <> showCyclicPath' ps

showCyclicPath' :: [Path Abs File] -> T.Text
showCyclicPath' pathList =
  case pathList of
    [] ->
      ""
    [path] ->
      "\n  ~> " <> T.pack (toFilePath path)
    (path : ps) ->
      "\n  ~> " <> T.pack (toFilePath path) <> showCyclicPath' ps

ensureFileExistence :: Meta -> Path Abs File -> WithEnv ()
ensureFileExistence m path = do
  b <- doesFileExist path
  if b
    then return ()
    else raiseError m $ "no such file: " <> T.pack (toFilePath path)

extract :: L.ByteString -> Path Abs Dir -> WithEnv ()
extract bytestr pkgPath =
  liftIO $ Tar.unpack (toFilePath pkgPath) $ Tar.read $ GZip.decompress bytestr

includeCore :: Meta -> [TreePlus] -> [TreePlus]
includeCore m treeList =
  case treeList of
    ((_, TreeNode [(_, TreeLeaf "no-implicit-core")]) : rest) ->
      rest
    _ ->
      ( m,
        TreeNode
          [ (m, TreeLeaf "include"),
            (m, TreeLeaf "library"),
            (m, TreeLeaf "\"core/core.neut\"")
          ]
      )
        : treeList

adjustPhase :: TreePlus -> WithEnv TreePlus
adjustPhase tree =
  case tree of
    (m, TreeLeaf x) -> do
      m' <- adjustPhase' m
      return (m', TreeLeaf x)
    (m, TreeNode ts) -> do
      m' <- adjustPhase' m
      ts' <- mapM adjustPhase ts
      return (m', TreeNode ts')

adjustPhase' :: Meta -> WithEnv Meta
adjustPhase' m = do
  i <- gets phase
  let (_, l, c) = metaLocation m
  return $ m {metaLocation = (i, l, c)}
