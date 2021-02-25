module Preprocess (preprocess) where

import Control.Monad.State.Lazy hiding (get)
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Hint
import Data.Ident
import qualified Data.IntMap as IntMap
import Data.MetaTerm
import Data.Platform
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Tree
import GHC.IO.Handle
import Path
import Path.IO
import Preprocess.Discern
import Preprocess.Interpret
import Preprocess.Tokenize
import Reduce.MetaTerm
import System.Exit
import System.Process hiding (env)
import Text.Read (readMaybe)

preprocess :: Path Abs File -> WithEnv [TreePlus]
preprocess mainFilePath = do
  pushTrace mainFilePath
  out <- visit mainFilePath
  -- forM_ out $ \k -> do
  --   p $ T.unpack $ showAsSExp k
  -- p "quitting."
  -- _ <- liftIO $ exitWith ExitSuccess
  modify (\env -> env {enumEnv = Map.empty})
  modify (\env -> env {revEnumEnv = Map.empty})
  return out

visit :: Path Abs File -> WithEnv [TreePlus]
visit path = do
  pushTrace path
  modify (\env -> env {fileEnv = Map.insert path VisitInfoActive (fileEnv env)})
  modify (\env -> env {phase = 1 + phase env})
  content <- liftIO $ TIO.readFile $ toFilePath path
  tokenize content >>= preprocess'

leave :: WithEnv [a]
leave = do
  path <- getCurrentFilePath
  popTrace
  modify (\env -> env {fileEnv = Map.insert path VisitInfoFinish (fileEnv env)})
  -- modify (\env -> env {prefixEnv = []})
  -- modify (\env -> env {sectionEnv = []})
  return []

pushTrace :: Path Abs File -> WithEnv ()
pushTrace path =
  modify (\env -> env {traceEnv = path : traceEnv env})

popTrace :: WithEnv ()
popTrace =
  modify (\env -> env {traceEnv = tail (traceEnv env)})

preprocess' :: [TreePlus] -> WithEnv [TreePlus]
preprocess' stmtList = do
  case stmtList of
    [] ->
      leave
    stmt : restStmtList -> do
      -- p $ "before AQ: " <> T.unpack (showAsSExp stmt)
      quotedStmt <- autoQuoteStmt stmt
      -- p $ "after AQ:  " <> T.unpack (showAsSExp quotedStmt)
      stmt'' <- autoThunkStmt quotedStmt
      preprocess'' [stmt''] restStmtList

preprocess'' :: [TreePlus] -> [TreePlus] -> WithEnv [TreePlus]
preprocess'' quotedStmtList restStmtList =
  case quotedStmtList of
    [] ->
      preprocess' restStmtList
    headStmt : quotedRestStmtList -> do
      case headStmt of
        (m, TreeNode ((_, TreeLeaf headAtom) : rest)) ->
          case headAtom of
            "auto-quote"
              | [(_, TreeLeaf name)] <- rest -> do
                modify (\env -> env {autoQuoteEnv = S.insert name (autoQuoteEnv env)})
                preprocess'' quotedRestStmtList restStmtList
              | otherwise ->
                raiseSyntaxError m "(auto-quote LEAF)"
            "auto-thunk"
              | [(_, TreeLeaf name)] <- rest -> do
                modify (\env -> env {autoThunkEnv = S.insert name (autoThunkEnv env)})
                preprocess'' quotedRestStmtList restStmtList
              | otherwise ->
                raiseSyntaxError m "(auto-thunk LEAF)"
            "declare-enum-meta"
              | (_, TreeLeaf name) : ts <- rest -> do
                xis <- interpretEnumItem m name ts
                insEnumEnv m name xis
                preprocess'' quotedRestStmtList restStmtList
              | otherwise ->
                raiseSyntaxError m "(enum LEAF TREE ... TREE)"
            "ensure"
              | [(_, TreeLeaf pkg), (mUrl, TreeLeaf urlStr)] <- rest -> do
                libDirPath <- getLibraryDirPath
                pkg' <- parseRelDir $ T.unpack pkg
                let pkgDirPath = libDirPath </> pkg'
                isAlreadyInstalled <- doesDirExist pkgDirPath
                when (not isAlreadyInstalled) $ do
                  ensureDir pkgDirPath
                  urlStr' <- readStrOrThrow mUrl urlStr
                  let curlCmd = proc "curl" ["-s", "-S", "-L", urlStr']
                  let tarCmd = proc "tar" ["xJf", "-", "-C", toFilePath pkg', "--strip-components=1"]
                  (_, Just stdoutHandler, Just curlErrorHandler, curlHandler) <-
                    liftIO $ createProcess curlCmd {cwd = Just (toFilePath libDirPath), std_out = CreatePipe, std_err = CreatePipe}
                  (_, _, Just tarErrorHandler, tarHandler) <-
                    liftIO $ createProcess tarCmd {cwd = Just (toFilePath libDirPath), std_in = UseHandle stdoutHandler, std_err = CreatePipe}
                  note' $ "downloading " <> pkg <> " from " <> T.pack urlStr'
                  curlExitCode <- liftIO $ waitForProcess curlHandler
                  raiseIfFailure mUrl "curl" curlExitCode curlErrorHandler pkgDirPath
                  note' $ "extracting " <> pkg <> " into " <> T.pack (toFilePath pkgDirPath)
                  tarExitCode <- liftIO $ waitForProcess tarHandler
                  raiseIfFailure mUrl "tar" tarExitCode tarErrorHandler pkgDirPath
                  return ()
                preprocess'' quotedRestStmtList restStmtList
              | otherwise ->
                raiseSyntaxError m "(ensure LEAF LEAF)"
            "include"
              | [(mPath, TreeLeaf pathString)] <- rest,
                not (T.null pathString) ->
                includeFile m mPath pathString quotedRestStmtList restStmtList
              | otherwise ->
                raiseSyntaxError m "(include LEAF)"
            "introspect"
              | ((mx, TreeLeaf x) : stmtClauseList) <- rest -> do
                val <- retrieveCompileTimeVarValue mx x
                stmtClauseList' <- mapM preprocessStmtClause stmtClauseList
                case lookup val stmtClauseList' of
                  Nothing ->
                    preprocess'' quotedRestStmtList restStmtList
                  Just as1 ->
                    preprocess'' (as1 ++ quotedRestStmtList) restStmtList
              | otherwise ->
                raiseSyntaxError m "(introspect LEAF TREE*)"
            "let-meta"
              | [(_, TreeLeaf name), body] <- rest -> do
                body' <- evaluate body
                name' <- newNameWith $ asIdent name
                modify (\env -> env {topMetaNameEnv = Map.insert name name' (topMetaNameEnv env)})
                modify (\env -> env {metaTermCtx = IntMap.insert (asInt name') body' (metaTermCtx env)})
                preprocess'' quotedRestStmtList restStmtList
              | otherwise ->
                raiseSyntaxError m "(let-meta LEAF TREE)"
            "statement-meta" ->
              preprocess'' (rest ++ quotedRestStmtList) restStmtList
            _ ->
              preprocessAux headStmt quotedRestStmtList restStmtList
        _ ->
          preprocessAux headStmt quotedRestStmtList restStmtList

preprocessAux :: TreePlus -> [TreePlus] -> [TreePlus] -> WithEnv [TreePlus]
preprocessAux headStmt expandedRestStmtList restStmtList = do
  headStmt' <- evaluate headStmt >>= specialize
  if isSpecialMetaForm headStmt'
    then preprocess'' (headStmt' : expandedRestStmtList) restStmtList
    else do
      treeList <- preprocess'' expandedRestStmtList restStmtList
      return $ headStmt' : treeList

evaluate :: TreePlus -> WithEnv MetaTermPlus
evaluate e = do
  ctx <- gets metaTermCtx
  interpretCode e >>= discernMetaTerm >>= return . substMetaTerm ctx >>= reduceMetaTerm

isSpecialMetaForm :: TreePlus -> Bool
isSpecialMetaForm tree =
  case tree of
    (_, TreeNode ((_, TreeLeaf x) : _)) ->
      S.member x metaKeywordSet
    _ ->
      False

metaKeywordSet :: S.Set T.Text
metaKeywordSet =
  S.fromList
    [ "auto-quote",
      "auto-thunk",
      "declare-enum-meta",
      "ensure",
      "include",
      "introspect",
      "let-meta",
      "statement-meta"
    ]

includeFile ::
  Hint ->
  Hint ->
  T.Text ->
  [TreePlus] ->
  [TreePlus] ->
  WithEnv [TreePlus]
includeFile m mPath pathString expandedRestStmtList as = do
  -- includeにはその痕跡を残しておいてもよいかも。Parse.hsのほうでこれを参照してなんかチェックする感じ。
  -- ensureEnvSanity m
  path <- readStrOrThrow mPath pathString
  when (null path) $ raiseError m "found an empty path"
  dirPath <-
    if head path == '.'
      then getCurrentDirPath
      else getLibraryDirPath
  newPath <- resolveFile dirPath path
  ensureFileExistence m newPath
  denv <- gets fileEnv
  case Map.lookup newPath denv of
    Just VisitInfoActive -> do
      tenv <- gets traceEnv
      let cyclicPath = dropWhile (/= newPath) (reverse tenv) ++ [newPath]
      raiseError m $ "found a cyclic inclusion:\n" <> showCyclicPath cyclicPath
    Just VisitInfoFinish ->
      preprocess'' expandedRestStmtList as
    Nothing -> do
      treeList1 <- visit newPath
      treeList2 <- preprocess'' expandedRestStmtList as
      return $ treeList1 ++ treeList2

readStrOrThrow :: (Read a) => Hint -> T.Text -> WithEnv a
readStrOrThrow m quotedStr =
  case readMaybe (T.unpack quotedStr) of
    Nothing ->
      raiseError m "the atom here must be a string"
    Just str ->
      return str

raiseIfFailure :: Hint -> String -> ExitCode -> Handle -> Path Abs Dir -> WithEnv ()
raiseIfFailure m procName exitCode h pkgDirPath =
  case exitCode of
    ExitSuccess ->
      return ()
    ExitFailure i -> do
      removeDir pkgDirPath -- cleanup
      errStr <- liftIO $ hGetContents h
      raiseError m $ T.pack $ "the child process `" ++ procName ++ "` failed with the following message (exitcode = " ++ show i ++ "):\n" ++ errStr

-- ensureEnvSanity :: Hint -> WithEnv ()
-- ensureEnvSanity m = do
--   penv <- gets prefixEnv
--   if null penv
--     then return ()
--     else raiseError m "`include` can only be used with no prefix assumption"

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

ensureFileExistence :: Hint -> Path Abs File -> WithEnv ()
ensureFileExistence m path = do
  b <- doesFileExist path
  if b
    then return ()
    else raiseError m $ "no such file: " <> T.pack (toFilePath path)

specialize :: MetaTermPlus -> WithEnv TreePlus
specialize term =
  case term of
    (m, MetaTermLeaf x) ->
      return (m, TreeLeaf x)
    (m, MetaTermNode es) -> do
      es' <- mapM specialize es
      return (m, TreeNode es')
    (m, _) -> do
      raiseError m $ "meta-reduction of this term resulted in a non-quoted term"

-- raiseError m $ "meta-reduction of this term resulted in a non-quoted term: " <> showAsSExp (toTree term)

preprocessStmtClause :: TreePlus -> WithEnv (T.Text, [TreePlus])
preprocessStmtClause tree =
  case tree of
    (_, TreeNode ((_, TreeLeaf x) : stmtList)) ->
      return (x, stmtList)
    (m, _) ->
      raiseSyntaxError m "(LEAF TREE*)"

retrieveCompileTimeVarValue :: Hint -> T.Text -> WithEnv T.Text
retrieveCompileTimeVarValue m var =
  case var of
    "OS" ->
      showOS <$> getOS
    "architecture" ->
      showArch <$> getArch
    _ ->
      raiseError m $ "no such compile-time variable defined: " <> var

mapStmt :: (TreePlus -> WithEnv TreePlus) -> TreePlus -> WithEnv TreePlus
mapStmt f tree =
  case tree of
    (m, TreeNode [l@(_, TreeLeaf "let-meta"), name, e]) -> do
      e' <- f e
      return (m, TreeNode [l, name, e'])
    (m, TreeNode (stmt@(_, TreeLeaf "statement-meta") : rest)) -> do
      rest' <- mapM (mapStmt f) rest
      return (m, TreeNode (stmt : rest'))
    _ ->
      if isSpecialMetaForm tree
        then return tree
        else f tree

autoThunkStmt :: TreePlus -> WithEnv TreePlus
autoThunkStmt =
  mapStmt autoThunk

autoThunk :: TreePlus -> WithEnv TreePlus
autoThunk tree = do
  tenv <- gets autoThunkEnv
  case tree of
    (_, TreeLeaf _) ->
      return tree
    (m, TreeNode ts) -> do
      ts' <- mapM autoThunk ts
      case ts' of
        t@(_, TreeLeaf x) : rest
          | S.member x tenv ->
            return (m, TreeNode $ t : map autoThunk' rest)
        _ ->
          return (m, TreeNode ts')

autoThunk' :: TreePlus -> TreePlus
autoThunk' (m, t) =
  (m, TreeNode [(m, TreeLeaf "lambda-meta"), (m, TreeNode []), (m, t)])

autoQuoteStmt :: TreePlus -> WithEnv TreePlus
autoQuoteStmt =
  mapStmt autoQuote

autoQuote :: TreePlus -> WithEnv TreePlus
autoQuote tree = do
  qenv <- gets autoQuoteEnv
  return $ autoQuote' qenv tree

autoQuote' :: S.Set T.Text -> TreePlus -> TreePlus
autoQuote' qenv tree =
  case tree of
    (_, TreeLeaf _) ->
      tree
    (m, TreeNode ts) -> do
      let modifier = if isSpecialForm qenv tree then quoteData else unquoteCode
      let ts' = map (modifier qenv . autoQuote' qenv) ts
      (m, TreeNode ts')

quoteData :: S.Set T.Text -> TreePlus -> TreePlus
quoteData qenv tree@(m, _) =
  if isSpecialForm qenv tree
    then tree
    else (m, TreeNode [(m, TreeLeaf "quasiquote"), tree])

unquoteCode :: S.Set T.Text -> TreePlus -> TreePlus
unquoteCode qenv tree@(m, _) =
  if isSpecialForm qenv tree
    then (m, TreeNode [(m, TreeLeaf "quasiunquote"), tree])
    else tree

isSpecialForm :: S.Set T.Text -> TreePlus -> Bool
isSpecialForm qenv tree =
  case tree of
    (_, TreeLeaf x) ->
      S.member x qenv
    (_, TreeNode ((_, TreeLeaf x) : _)) ->
      S.member x qenv
    _ ->
      False
