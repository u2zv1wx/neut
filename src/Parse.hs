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

parse :: Path Abs File -> WithEnv WeakStmt
parse inputPath = do
  stmtList <- visit inputPath
  stmtList' <- discern stmtList
  warnUnusedVar
  pushTrace inputPath
  concatQuasiStmtList stmtList'

visit :: Path Abs File -> WithEnv [QuasiStmt]
visit path = do
  insDepGraph path
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

insDepGraph :: Path Abs File -> WithEnv ()
insDepGraph path = do
  tenv <- gets traceEnv
  case tenv of
    [] -> return ()
    (foo : _) ->
      modify
        (\env -> env {depGraph = Map.insertWith (++) foo [path] (depGraph env)})

pushTrace :: Path Abs File -> WithEnv ()
pushTrace path = modify (\env -> env {traceEnv = path : traceEnv env})

popTrace :: WithEnv ()
popTrace = modify (\env -> env {traceEnv = tail (traceEnv env)})

parse' :: [TreePlus] -> WithEnv [QuasiStmt]
parse' =
  \case
    [] -> leave
    (stmt : cont) ->
      case stmt of
        (m, TreeNode ((_, TreeLeaf "notation") : es))
          | [from, to] <- es -> do
            checkNotationSanity from
            modify (\e -> e {notationEnv = (from, to) : notationEnv e})
            parse' cont
          | otherwise -> raiseSyntaxError m "(notation TREE TREE)"
        (m, TreeNode ((_, TreeLeaf "keyword") : es))
          | [(_, TreeLeaf s)] <- es -> do
            checkKeywordSanity m s
            modify (\e -> e {keywordEnv = S.insert s (keywordEnv e)})
            parse' cont
          | otherwise -> raiseSyntaxError m "(keyword LEAF)"
        (m, TreeNode ((_, TreeLeaf "use") : es))
          | [(_, TreeLeaf s)] <- es ->
            use s >> parse' cont
          | otherwise -> raiseSyntaxError m "(use LEAF)"
        (m, TreeNode ((_, TreeLeaf "unuse") : es))
          | [(_, TreeLeaf s)] <- es ->
            unuse s >> parse' cont
          | otherwise -> raiseSyntaxError m "(unuse LEAF)"
        (m, TreeNode ((_, TreeLeaf "section") : es))
          | [(_, TreeLeaf s)] <- es -> do
            modify (\e -> e {sectionEnv = s : sectionEnv e})
            getCurrentSection >>= use
            parse' cont
          | otherwise -> raiseSyntaxError m "(section LEAF)"
        (m, TreeNode ((_, TreeLeaf "end") : es))
          | [(_, TreeLeaf s)] <- es -> do
            ns <- gets sectionEnv
            case ns of
              [] -> raiseError m "there is no section to end"
              (s' : ns')
                | s == s' -> do
                  getCurrentSection >>= unuse
                  modify (\e -> e {sectionEnv = ns'})
                  parse' cont
                | otherwise ->
                  raiseError m $
                    "the innermost section is not `" <> s <> "`, but is `" <> s' <> "`"
          | otherwise -> raiseSyntaxError m "(end LEAF)"
        (m, TreeNode ((_, TreeLeaf "enum") : rest))
          | (_, TreeLeaf name) : ts <- rest -> do
            m' <- adjustPhase' m
            xis <- interpretEnumItem m' name ts
            insEnumEnv m' name xis
            parse' cont
          | otherwise -> raiseSyntaxError m "(enum LEAF TREE ... TREE)"
        (m, TreeNode ((_, TreeLeaf "include") : rest))
          | [(mPath, TreeLeaf pathString)] <- rest ->
            includeFile m mPath pathString getCurrentDirPath cont
          | [(_, TreeLeaf "library"), (mPath, TreeLeaf pathString)] <- rest ->
            includeFile m mPath pathString getLibraryDirPath cont
          | otherwise -> raiseSyntaxError m "(include LEAF) | (include library LEAF)"
        (m, TreeNode ((_, TreeLeaf "ensure") : rest))
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
            parse' cont
          | otherwise -> raiseSyntaxError m "(ensure LEAF LEAF)"
        (_, TreeNode ((_, TreeLeaf "statement") : innerCont)) -> parse' $ innerCont ++ cont
        (m, TreeNode ((_, TreeLeaf "introspect") : rest))
          | ((mx, TreeLeaf x) : stmtClauseList) <- rest -> do
            val <- retrieveCompileTimeVarValue mx x
            stmtClauseList' <- mapM parseStmtClause stmtClauseList
            case lookup val stmtClauseList' of
              Nothing -> parse' cont
              Just as1 -> parse' $ as1 ++ cont
          | otherwise -> raiseSyntaxError m "(introspect LEAF TREE*)"
        (m, TreeNode ((_, TreeLeaf "constant") : rest))
          | [(_, TreeLeaf name), t] <- rest -> do
            t' <- adjustPhase t >>= macroExpand >>= interpret >>= discernWithCurrentNameEnv
            m' <- adjustPhase' m
            name' <- withSectionPrefix name
            insertConstant m' name'
            h <- asIdent <$> newTextWith "_"
            let constDecl = QuasiStmtLet m' (m', h, t') (m', WeakTermConst name')
            defList <- parse' cont
            return $ constDecl : defList
          | otherwise -> raiseSyntaxError m "(constant LEAF TREE)"
        (m, TreeNode (def@(mDef, TreeLeaf "definition") : rest))
          | [name@(_, TreeLeaf _), body] <- rest ->
            parse' $ (m, TreeNode [(mDef, TreeLeaf "let"), name, body]) : cont
          | name@(mFun, TreeLeaf _) : xts@(_, TreeNode _) : body : rest' <- rest ->
            parse' $ (m, TreeNode [def, (mFun, TreeNode (name : xts : body : rest'))]) : cont
          | otherwise -> do
            ss1 <- parseDef rest
            ss2 <- parse' cont
            return $ ss1 ++ ss2
        (m, TreeNode (ind@(_, TreeLeaf "inductive") : rest))
          | name@(mFun, TreeLeaf _) : xts@(_, TreeNode _) : rest' <- rest ->
            parse' $ (m, TreeNode [ind, (mFun, TreeNode (name : xts : rest'))]) : cont
          | otherwise -> do
            rest' <- mapM (adjustPhase >=> macroExpand) rest
            m' <- adjustPhase' m
            stmtList1 <- parseInductive m' rest'
            stmtList2 <- parse' cont
            return $ stmtList1 ++ stmtList2
        (m, TreeNode (coind@(_, TreeLeaf "coinductive") : rest))
          | name@(mFun, TreeLeaf _) : xts@(_, TreeNode _) : rest' <- rest ->
            parse' $ (m, TreeNode [coind, (mFun, TreeNode (name : xts : rest'))]) : cont
          | otherwise -> do
            rest' <- mapM (adjustPhase >=> macroExpand) rest
            registerLabelInfo rest'
            rest'' <- asInductive rest'
            stmtList1 <- parseInductive m rest''
            stmtList2 <- generateProjections rest'
            stmtList3 <- parse' cont
            return $ stmtList1 ++ stmtList2 ++ stmtList3
        (m, TreeNode ((mLet, TreeLeaf "let") : rest))
          | [(mx, TreeLeaf x), t, e] <- rest -> do
            let xt = (mx, TreeNode [(mx, TreeLeaf x), t])
            parse' ((m, TreeNode [(mLet, TreeLeaf "let"), xt, e]) : cont)
          | [xt, e] <- rest -> do
            m' <- adjustPhase' m
            e' <- adjustPhase e >>= macroExpand >>= interpret
            xt' <- adjustPhase xt >>= macroExpand >>= prefixTextPlus >>= interpretIdentPlus
            defList <- parse' cont
            return $ QuasiStmtLet m' xt' e' : defList
          | otherwise -> raiseSyntaxError m "(let LEAF TREE TREE) | (let TREE TREE)"
        (m, TreeNode ((_, TreeLeaf "verify") : rest))
          | [e] <- rest -> do
            e' <- adjustPhase e >>= macroExpand >>= interpret
            m' <- adjustPhase' m
            defList <- parse' cont
            return $ QuasiStmtVerify m' e' : defList
          | otherwise -> raiseSyntaxError m "(verify LEAF) | (verify library LEAF)"
        _ -> do
          e <- adjustPhase stmt >>= macroExpand
          if isSpecialForm e
            then parse' $ e : cont
            else do
              e' <- interpret e
              name <- asIdent <$> newTextWith "_"
              m' <- adjustPhase' $ metaOf e'
              t <- newHole m'
              defList <- parse' cont
              return $ QuasiStmtLet m' (m', name, t) e' : defList

use :: T.Text -> WithEnv ()
use s =
  modify (\e -> e {prefixEnv = s : prefixEnv e})

unuse :: T.Text -> WithEnv ()
unuse s =
  modify (\e -> e {prefixEnv = filter (/= s) (prefixEnv e)})

withSectionPrefix :: T.Text -> WithEnv T.Text
withSectionPrefix x = do
  ns <- gets sectionEnv
  return $ foldl (\acc n -> n <> ":" <> acc) x ns

getCurrentSection :: WithEnv T.Text
getCurrentSection = do
  ns <- gets sectionEnv
  return $ getCurrentSection' ns

getCurrentSection' :: [T.Text] -> T.Text
getCurrentSection' =
  \case
    [] -> ""
    [n] -> n
    (n : ns) -> getCurrentSection' ns <> ":" <> n

asInductive :: [TreePlus] -> WithEnv [TreePlus]
asInductive =
  \case
    [] -> return []
    (t : ts) -> do
      (sub, t') <- asInductive' t
      ts' <- asInductive $ map (substTree sub) ts
      return $ t' : ts'

asInductive' :: TreePlus -> WithEnv ((T.Text, T.Text), TreePlus)
asInductive' (m, TreeNode ((_, TreeLeaf a) : (_, TreeNode xts) : rules)) = do
  let a' = "(" <> a <> ")"
  let sub = (a, a')
  let xts' = map (substTree sub) xts
  rules'' <- mapM styleRule $ map (substTree sub) rules
  let hole = "(_)"
  argList <- mapM extractArg xts
  return
    ( (a, a'),
      ( m,
        TreeNode
          [ (m, TreeLeaf a),
            (m, TreeNode xts'),
            ( m,
              TreeNode
                [ (m, TreeLeaf "unfold"),
                  ( m,
                    TreeNode
                      ( [ ( m,
                            TreeNode
                              [ (m, TreeLeaf a'),
                                ( m,
                                  TreeNode
                                    [ (m, TreeLeaf "pi"),
                                      (m, TreeNode xts'),
                                      (m, TreeLeaf "tau")
                                    ]
                                )
                              ]
                          )
                        ]
                          ++ rules''
                          ++ [ ( m,
                                 TreeNode
                                   [ (m, TreeLeaf hole),
                                     (m, TreeNode ((m, TreeLeaf a') : argList))
                                   ]
                               )
                             ]
                      )
                  ),
                  (m, TreeNode ((m, TreeLeaf a) : argList))
                ]
            )
          ]
      )
    )
asInductive' t = raiseSyntaxError (fst t) "(LEAF (TREE ... TREE) ...)"

extractArg :: TreePlus -> WithEnv TreePlus
extractArg =
  \case
    (m, TreeLeaf x) -> return (m, TreeLeaf x)
    (_, TreeNode [(m, TreeLeaf x), _]) -> return (m, TreeLeaf x)
    t -> raiseSyntaxError (fst t) "LEAF | (LEAF TREE)"

styleRule :: TreePlus -> WithEnv TreePlus
styleRule =
  \case
    (m, TreeNode [(mName, TreeLeaf name), (_, TreeNode xts), t]) ->
      return
        ( m,
          TreeNode
            [ (mName, TreeLeaf name),
              (m, TreeNode [(m, TreeLeaf "pi"), (m, TreeNode xts), t])
            ]
        )
    t -> raiseSyntaxError (fst t) "(LEAF (TREE ... TREE) TREE)"

readStrOrThrow :: (Read a) => Meta -> T.Text -> WithEnv a
readStrOrThrow m quotedStr =
  case readMaybe (T.unpack quotedStr) of
    Nothing -> raiseError m "the atom here must be a string"
    Just str -> return str

includeFile ::
  Meta ->
  Meta ->
  T.Text ->
  WithEnv (Path Abs Dir) ->
  [TreePlus] ->
  WithEnv [QuasiStmt]
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
    Just VisitInfoFinish -> parse' as
    Nothing -> do
      includedQuasiStmtList <- visit newPath
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

parseDef :: [TreePlus] -> WithEnv [QuasiStmt]
parseDef xds = do
  xds' <- mapM (adjustPhase >=> prefixFunName >=> macroExpand) xds
  -- ここでいい感じにdiscernを行う必要がある
  xds'' <- mapM interpretIter xds'
  let baseSub = Map.fromList $ map defToSub xds''
  let sub = selfCompose (length baseSub) baseSub
  let varList = map (\(_, (m, x, _), _, _) -> (m, WeakTermUpsilon x)) xds''
  let iterList = map (substWeakTermPlus sub) varList -- fixme: ここのsubstはintじゃなく名前に沿ったものにしないとだめ
  xs <- mapM extractFunName xds'
  return (toLetList $ zip (zip xs xds'') iterList)

prefixFunName :: TreePlus -> WithEnv TreePlus
prefixFunName =
  \case
    (m, TreeNode [xt, xts, body]) -> do
      xt' <- prefixTextPlus xt
      return (m, TreeNode [xt', xts, body])
    t -> raiseSyntaxError (fst t) "(TREE TREE TREE)"

prefixTextPlus :: TreePlus -> WithEnv TreePlus
prefixTextPlus =
  \case
    (m, TreeLeaf "_") -> return (m, TreeLeaf "_")
    (m, TreeLeaf x) -> do
      x' <- withSectionPrefix x
      return (m, TreeLeaf x')
    (m, TreeNode [(mx, TreeLeaf "_"), t]) ->
      return (m, TreeNode [(mx, TreeLeaf "_"), t])
    (m, TreeNode [(mx, TreeLeaf x), t]) -> do
      x' <- withSectionPrefix x
      return (m, TreeNode [(mx, TreeLeaf x'), t])
    t -> raiseSyntaxError (fst t) "LEAF | (LEAF TREE)"

extractFunName :: TreePlus -> WithEnv Ident
extractFunName =
  \case
    (_, TreeNode ((_, TreeLeaf x) : _)) -> return $ asIdent x
    (_, TreeNode ((_, TreeNode [(_, TreeLeaf x), _]) : _)) -> return $ asIdent x
    t -> raiseSyntaxError (fst t) "(LEAF ...) | ((LEAF TREE) ...)"

toLetList :: [(IdentDef, WeakTermPlus)] -> [QuasiStmt]
toLetList =
  \case
    [] -> []
    (((x, (m, (mx, _, t), _, _)), iter) : rest) -> QuasiStmtLet m (mx, x, t) iter : toLetList rest

defToSub :: Def -> (Key, WeakTermPlus)
defToSub (m, (mx, x, t), xts, e) =
  (Left $ asInt x, (m, WeakTermIter (mx, x, t) xts e))

selfCompose :: Int -> SubstWeakTerm -> SubstWeakTerm
selfCompose i sub =
  if i == 0
    then sub
    else compose sub $ selfCompose (i - 1) sub

-- fixme: ここではintじゃなくてフルで比較するタイプのsubstを行う必要がある (discern以前にsubstをするので)
compose :: SubstWeakTerm -> SubstWeakTerm -> SubstWeakTerm
compose s1 s2 = Map.union (Map.map (substWeakTermPlus s1) s2) s1

parseStmtClause :: TreePlus -> WithEnv (T.Text, [TreePlus])
parseStmtClause =
  \case
    (_, TreeNode ((_, TreeLeaf x) : stmtList)) -> return (x, stmtList)
    (m, _) -> raiseSyntaxError m "(LEAF TREE*)"

retrieveCompileTimeVarValue :: Meta -> T.Text -> WithEnv T.Text
retrieveCompileTimeVarValue m var =
  case var of
    "OS" -> showOS <$> getOS
    "architecture" -> showArch <$> getArch
    _ -> raiseError m $ "no such compile-time variable defined: " <> var

isSpecialForm :: TreePlus -> Bool
isSpecialForm =
  \case
    (_, TreeNode ((_, TreeLeaf x) : _)) -> S.member x keywordSet
    _ -> False

keywordSet :: S.Set T.Text
keywordSet =
  S.fromList
    [ "notation",
      "keyword",
      "enum",
      "include",
      "ensure",
      "constant",
      "use",
      "unuse",
      "section",
      "end",
      "statement",
      "introspect",
      "let",
      "definition",
      "inductive",
      "coinductive"
    ]

concatQuasiStmtList :: [QuasiStmt] -> WithEnv WeakStmt
concatQuasiStmtList =
  \case
    [] -> do
      path <- getCurrentFilePath
      content <- liftIO $ TIO.readFile $ toFilePath path
      let m = newMeta (length $ T.lines content) 1 path
      return $ WeakStmtReturn (m, WeakTermEnumIntro $ EnumValueIntS 64 0)
    QuasiStmtLet m xt e : es -> do
      cont <- concatQuasiStmtList es
      return $ WeakStmtLet m xt e cont
    QuasiStmtLetWT m xt e : es -> do
      cont <- concatQuasiStmtList es
      return $ WeakStmtLetWT m xt e cont
    QuasiStmtVerify m e : es -> do
      cont <- concatQuasiStmtList es
      return $ WeakStmtVerify m e cont
    QuasiStmtLetInductive n m at e : es -> do
      insForm n at e
      cont <- concatQuasiStmtList es
      return $ WeakStmtLetWT m at e cont
    QuasiStmtLetInductiveIntro m bt e as : ss ->
      case e of
        (mLam, WeakTermPiIntro Nothing xtsyts (_, WeakTermPiIntro (Just (bi, _)) atsbts (_, WeakTermPiElim b _))) -> do
          (_, is) <- lookupRevIndEnv m bi
          yts' <- mapM (internalize as atsbts) $ drop (length (is :: [Int])) xtsyts
          insInductive as bt -- register the constructor (if necessary)
          cont <- concatQuasiStmtList ss
          return $
            WeakStmtLetWT
              m
              bt
              ( mLam, -- metaIsReducible mLam == False
                weakTermPiIntro
                  xtsyts
                  ( m,
                    WeakTermPiIntro
                      (Just (bi, xtsyts))
                      atsbts
                      (m, WeakTermPiElim b yts')
                  )
              )
              cont
        _ -> raiseCritical m "inductive-intro"

checkKeywordSanity :: Meta -> T.Text -> WithEnv ()
checkKeywordSanity m x
  | x == "" = raiseError m "empty string for a keyword"
  | T.last x == '+' = raiseError m "A +-suffixed name cannot be a keyword"
  | otherwise = return ()

showCyclicPath :: [Path Abs File] -> T.Text
showCyclicPath =
  \case
    [] -> ""
    [path] -> T.pack (toFilePath path)
    (path : ps) -> "     " <> T.pack (toFilePath path) <> showCyclicPath' ps

showCyclicPath' :: [Path Abs File] -> T.Text
showCyclicPath' =
  \case
    [] -> ""
    [path] -> "\n  ~> " <> T.pack (toFilePath path)
    (path : ps) -> "\n  ~> " <> T.pack (toFilePath path) <> showCyclicPath' ps

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
    ((_, TreeNode [(_, TreeLeaf "no-implicit-core")]) : rest) -> rest
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
adjustPhase =
  \case
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

warnUnusedVar :: WithEnv ()
warnUnusedVar =
  whenCheck $ do
    set <- gets intactSet
    let set' = S.map (\(m, x) -> (getPosInfo m, x)) set
    warnUnusedVar' $ S.toList set'

warnUnusedVar' :: [(PosInfo, T.Text)] -> WithEnv ()
warnUnusedVar' =
  \case
    [] -> return ()
    ((pos, x) : pxs)
      | T.all (`S.notMember` S.fromList "()") x -> do
        warn pos $ "defined but not used: `" <> x <> "`"
        warnUnusedVar' pxs
      | otherwise -> warnUnusedVar' pxs
