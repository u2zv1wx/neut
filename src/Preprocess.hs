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
  out' <- mapM specialize out
  forM_ out' $ \k -> do
    p $ T.unpack $ showAsSExp k
  p "quitting."
  modify (\env -> env {enumEnv = Map.empty})
  modify (\env -> env {revEnumEnv = Map.empty})
  _ <- liftIO $ exitWith ExitSuccess
  undefined

visit :: Path Abs File -> WithEnv [MetaTermPlus]
visit path = do
  pushTrace path
  modify (\env -> env {fileEnv = Map.insert path VisitInfoActive (fileEnv env)})
  modify (\env -> env {phase = 1 + phase env})
  content <- liftIO $ TIO.readFile $ toFilePath path
  tokenize content >>= preprocess' IntMap.empty

leave :: WithEnv [MetaTermPlus]
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

preprocess' :: SubstMetaTerm -> [TreePlus] -> WithEnv [MetaTermPlus]
preprocess' sub stmtList = do
  case stmtList of
    [] ->
      leave
    headStmt : restStmtList -> do
      case headStmt of
        (m, TreeNode ((_, TreeLeaf headAtom) : rest)) ->
          case headAtom of
            -- "auto-quote"
            --   | [(_, MetaTermLeaf name)] <- rest -> do
            --     modify (\env -> env {autoQuoteEnv = S.insert name (autoQuoteEnv env)})
            --     preprocess' sub restStmtList
            --   | otherwise ->
            --     raiseSyntaxError m "(auto-quote LEAF)"
            "LET"
              | [(_, TreeLeaf name), body] <- rest -> do
                body' <- interpretCode body >>= discernMetaTerm
                name' <- newNameWith $ asIdent name
                body'' <- reduceMetaTerm $ substMetaTerm sub body'
                modify (\env -> env {topMetaNameEnv = Map.insert name name' (topMetaNameEnv env)})
                preprocess' (IntMap.insert (asInt name') body'' sub) restStmtList
              | otherwise -> do
                raiseSyntaxError m "(denote LEAF TREE)"
            "meta-enum"
              | (_, TreeLeaf name) : ts <- rest -> do
                xis <- interpretEnumItem m name ts
                insEnumEnv m name xis
                preprocess' sub restStmtList
              | otherwise ->
                raiseSyntaxError m "(enum LEAF TREE ... TREE)"
            "meta-constant"
              | [(_, TreeLeaf name)] <- rest -> do
                modify (\env -> env {metaConstantSet = S.insert name (metaConstantSet env)})
                preprocess' sub restStmtList
              | otherwise ->
                raiseSyntaxError m "(meta-constant LEAF)"
            "include"
              | [(mPath, TreeLeaf pathString)] <- rest,
                not (T.null pathString) ->
                includeFile sub m mPath pathString restStmtList
              | otherwise ->
                raiseSyntaxError m "(include LEAF)"
            "introspect"
              | ((mx, TreeLeaf x) : stmtClauseList) <- rest -> do
                val <- retrieveCompileTimeVarValue mx x
                stmtClauseList' <- mapM preprocessStmtClause stmtClauseList
                case lookup val stmtClauseList' of
                  Nothing ->
                    preprocess' sub restStmtList
                  Just as1 ->
                    preprocess' sub $ as1 ++ restStmtList
              | otherwise ->
                raiseSyntaxError m "(introspect LEAF TREE*)"
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
                preprocess' sub restStmtList
              | otherwise ->
                raiseSyntaxError m "(ensure LEAF LEAF)"
            "statement" ->
              preprocess' sub $ rest ++ restStmtList
            _ ->
              preprocessAux sub headStmt restStmtList
        _ ->
          preprocessAux sub headStmt restStmtList

preprocessAux :: SubstMetaTerm -> TreePlus -> [TreePlus] -> WithEnv [MetaTermPlus]
preprocessAux sub headStmt restStmtList = do
  headStmt' <- interpretCode headStmt >>= discernMetaTerm
  headStmt'' <- reduceMetaTerm $ substMetaTerm sub headStmt'
  case headStmt'' of
    (_, MetaTermLeaf _) -> do
      treeList <- preprocess' sub restStmtList
      return $ headStmt'' : treeList
    e@(_, MetaTermNode _) -> do
      -- denote xとかを生成するやつ
      if isSpecialMetaForm e
        then preprocess' sub $ toTree e : restStmtList
        else do
          treeList <- preprocess' sub restStmtList
          return $ headStmt'' : treeList
    _ -> do
      p' headStmt''
      raiseError (fst headStmt') $ "meta-computation resulted in a non-quoted term: " <> showAsSExp (toTree headStmt'')

isSpecialMetaForm :: MetaTermPlus -> Bool
isSpecialMetaForm tree =
  case tree of
    (_, MetaTermNode ((_, MetaTermLeaf x) : _)) ->
      S.member x metaKeywordSet
    _ ->
      False

metaKeywordSet :: S.Set T.Text
metaKeywordSet =
  S.fromList
    [ "LET",
      "statement",
      "include",
      -- "auto-thunk",
      -- "auto-quote",
      "meta-enum",
      "introspect",
      "meta-constant",
      "ensure"
    ]

includeFile ::
  SubstMetaTerm ->
  Hint ->
  Hint ->
  T.Text ->
  [TreePlus] ->
  WithEnv [MetaTermPlus]
includeFile sub m mPath pathString as = do
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
      preprocess' sub as
    Nothing -> do
      treeList1 <- visit newPath
      treeList2 <- preprocess' sub as
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
      p' term
      raiseError m "the argument isn't a valid AST"

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