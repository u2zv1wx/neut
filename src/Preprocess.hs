module Preprocess (preprocess) where

import Control.Monad.State.Lazy hiding (get)
import Data.Basic
import Data.Env
import qualified Data.HashMap.Lazy as Map
import qualified Data.IntMap as IntMap
import Data.Log
import Data.MetaTerm
import Data.Namespace
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
import qualified System.Info as System
import System.Process hiding (env)
import Text.Read (readMaybe)

preprocess :: Path Abs File -> Compiler [TreePlus]
preprocess mainFilePath = do
  pushTrace mainFilePath
  -- out <- visit mainFilePath
  -- forM_ out $ \t ->
  --   liftIO $ putStrLn $ T.unpack (showAsSExp t)
  -- _ <- liftIO $ exitWith ExitSuccess
  visit mainFilePath

visit :: Path Abs File -> Compiler [TreePlus]
visit path = do
  pushTrace path
  modify (\env -> env {fileEnv = Map.insert path VisitInfoActive (fileEnv env)})
  content <- liftIO $ TIO.readFile $ toFilePath path
  tokenize content >>= preprocess'

leave :: Compiler [TreePlus]
leave = do
  path <- getCurrentFilePath
  modify (\env -> env {fileEnv = Map.insert path VisitInfoFinish (fileEnv env)})
  popTrace
  return []

pushTrace :: Path Abs File -> Compiler ()
pushTrace path =
  modify (\env -> env {traceEnv = path : traceEnv env})

popTrace :: Compiler ()
popTrace =
  modify (\env -> env {traceEnv = tail (traceEnv env)})

preprocess' :: [TreePlus] -> Compiler [TreePlus]
preprocess' stmtList = do
  case stmtList of
    [] -> do
      endStmtList <- generateEndStmtList
      unuseStmtList <- generateUnuseStmtList
      removeStmtList <- generateRemovePrefixStmtList
      case (endStmtList, unuseStmtList, removeStmtList) of
        (_ : _, _, _) ->
          preprocess' endStmtList
        (_, _ : _, _) ->
          preprocess' unuseStmtList
        (_, _, _ : _) ->
          preprocess' removeStmtList
        ([], [], []) ->
          leave
    headStmt : restStmtList ->
      case headStmt of
        (m, TreeNode (leaf@(_, TreeLeaf headAtom) : rest)) ->
          case headAtom of
            --
            -- basic statements
            --
            "define-macro"
              | [(_, TreeLeaf name), body] <- rest -> do
                nenv <- gets topMetaNameEnv
                when (Map.member name nenv) $
                  raiseError m $ "the meta-variable `" <> name <> "` is already defined at the top level"
                body' <- evaluate body
                name' <- withSectionPrefix name
                name'' <- newIdentFromIdent $ asIdent name'
                modify (\env -> env {topMetaNameEnv = Map.insert name' name'' (topMetaNameEnv env)})
                modify (\env -> env {metaTermCtx = IntMap.insert (asInt name'') body' (metaTermCtx env)})
                preprocess' restStmtList
              | [name@(_, TreeLeaf _), xts, body] <- rest -> do
                let defFix = (m, TreeNode [leaf, name, (m, TreeNode [(m, TreeLeaf "fix-meta"), name, xts, body])])
                preprocess' $ defFix : restStmtList
              | otherwise ->
                raiseSyntaxError m "(define-macro LEAF TREE) | (define-macro LEAF TREE TREE)"
            "define-macro-variadic"
              | [name@(_, TreeLeaf _), xts, body] <- rest -> do
                let defFix = (m, TreeNode [(m, TreeLeaf "define-macro"), name, (m, TreeNode [(m, TreeLeaf "fix-meta-variadic"), name, xts, body])])
                preprocess' $ defFix : restStmtList
              | otherwise ->
                raiseSyntaxError m "(define-macro-variadic LEAF TREE TREE)"
            --
            -- file-related statements
            --
            "include"
              | [(mPath, TreeLeaf pathString)] <- rest,
                not (T.null pathString) ->
                includeFile m mPath pathString restStmtList
              | otherwise ->
                raiseSyntaxError m "(include LEAF)"
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
                preprocess' restStmtList
              | otherwise ->
                raiseSyntaxError m "(ensure LEAF LEAF)"
            --
            -- namespace-related statements
            --
            "section"
              | [(_, TreeLeaf s)] <- rest -> do
                treeList <- handleSection s (preprocess' restStmtList)
                return $ headStmt : treeList -- `(section NAME)` is also used in the object language
              | otherwise ->
                raiseSyntaxError m "(section LEAF)"
            "end"
              | [(_, TreeLeaf s)] <- rest -> do
                treeList <- handleEnd m s (preprocess' restStmtList)
                return $ headStmt : treeList -- `(end NAME)` is also used in the object language
              | otherwise ->
                raiseSyntaxError m "(end LEAF)"
            "define-prefix"
              | [(_, TreeLeaf from), (_, TreeLeaf to)] <- rest -> do
                modify (\env -> env {nsEnv = (from, to) : (nsEnv env)})
                treeList <- preprocess' restStmtList
                return $ headStmt : treeList
              | otherwise ->
                raiseSyntaxError m "(define-prefix LEAF LEAF)"
            "remove-prefix"
              | [(_, TreeLeaf from), (_, TreeLeaf to)] <- rest -> do
                modify (\env -> env {nsEnv = (filter (/= (from, to))) (nsEnv env)})
                treeList <- preprocess' restStmtList
                return $ headStmt : treeList
              | otherwise ->
                raiseSyntaxError m "(remove-prefix LEAF LEAF)"
            "use"
              | [(_, TreeLeaf s)] <- rest -> do
                treeList <- use s >> preprocess' restStmtList
                return $ headStmt : treeList -- the `(use NAME)` is also used in the object language
              | otherwise ->
                raiseSyntaxError m "(use LEAF)"
            "unuse"
              | [(_, TreeLeaf s)] <- rest -> do
                treeList <- unuse s >> preprocess' restStmtList
                return $ headStmt : treeList -- the `(unuse NAME)` is also used in the object language
              | otherwise ->
                raiseSyntaxError m "(unuse LEAF)"
            --
            -- other statements
            --
            "introspect"
              | ((mx, TreeLeaf x) : stmtClauseList) <- rest -> do
                val <- retrieveCompileTimeVarValue mx x
                stmtClauseList' <- mapM preprocessStmtClause stmtClauseList
                case lookup val stmtClauseList' of
                  Nothing ->
                    preprocess' restStmtList
                  Just as1 ->
                    preprocess' $ as1 ++ restStmtList
              | otherwise ->
                raiseSyntaxError m "(introspect LEAF TREE*)"
            "dry-expand"
              | [e] <- rest -> do
                e' <- autoQuote e >>= evaluate >>= specialize
                note m (showAsSExp e')
                preprocess' restStmtList
              | otherwise ->
                raiseSyntaxError m "(dry-expand TREE)"
            _ ->
              preprocessAux headStmt restStmtList
        _ ->
          preprocessAux headStmt restStmtList

preprocessAux :: TreePlus -> [TreePlus] -> Compiler [TreePlus]
preprocessAux headStmt restStmtList = do
  headStmt' <- autoQuote headStmt >>= evaluate >>= specialize
  treeList <- preprocess' restStmtList
  return $ headStmt' : treeList

evaluate :: TreePlus -> Compiler MetaTermPlus
evaluate e =
  interpretCode e >>= discernMetaTerm >>= reduceMetaTerm

includeFile ::
  Hint ->
  Hint ->
  T.Text ->
  [TreePlus] ->
  Compiler [TreePlus]
includeFile m mPath pathString as = do
  ensureEnvSanity m
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
      preprocess' as
    Nothing -> do
      treeList1 <- visit newPath
      treeList2 <- preprocess' as
      return $ treeList1 ++ treeList2

readStrOrThrow :: (Read a) => Hint -> T.Text -> Compiler a
readStrOrThrow m quotedStr =
  case readMaybe (T.unpack quotedStr) of
    Nothing ->
      raiseError m "the atom here must be a string"
    Just str ->
      return str

raiseIfFailure :: Hint -> String -> ExitCode -> Handle -> Path Abs Dir -> Compiler ()
raiseIfFailure m procName exitCode h pkgDirPath =
  case exitCode of
    ExitSuccess ->
      return ()
    ExitFailure i -> do
      removeDir pkgDirPath -- cleanup
      errStr <- liftIO $ hGetContents h
      raiseError m $ T.pack $ "the child process `" ++ procName ++ "` failed with the following message (exitcode = " ++ show i ++ "):\n" ++ errStr

ensureEnvSanity :: Hint -> Compiler ()
ensureEnvSanity m = do
  penv <- gets prefixEnv
  if null penv
    then return ()
    else raiseError m "`include` can only be used with no `use`"

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

ensureFileExistence :: Hint -> Path Abs File -> Compiler ()
ensureFileExistence m path = do
  b <- doesFileExist path
  if b
    then return ()
    else raiseError m $ "no such file: " <> T.pack (toFilePath path)

specialize :: MetaTermPlus -> Compiler TreePlus
specialize term =
  case term of
    (m, MetaTermLeaf x) ->
      return (m, TreeLeaf x)
    (m, MetaTermNode es) -> do
      es' <- mapM specialize es
      return (m, TreeNode es')
    (m, _) -> do
      p' term
      raiseError m $ "meta-reduction of this term resulted in a non-quoted term"

preprocessStmtClause :: TreePlus -> Compiler (T.Text, [TreePlus])
preprocessStmtClause tree =
  case tree of
    (_, TreeNode ((_, TreeLeaf x) : stmtList)) ->
      return (x, stmtList)
    (m, _) ->
      raiseSyntaxError m "(LEAF TREE*)"

retrieveCompileTimeVarValue :: Hint -> T.Text -> Compiler T.Text
retrieveCompileTimeVarValue m var =
  case var of
    "OS" ->
      return $ T.pack $ System.os
    "architecture" ->
      return $ T.pack $ System.arch
    _ ->
      raiseError m $ "no such compile-time variable defined: " <> var

autoQuote :: TreePlus -> Compiler TreePlus
autoQuote tree = do
  nenv <- gets topMetaNameEnv
  autoQuote' nenv tree

autoQuote' :: Map.HashMap T.Text Ident -> TreePlus -> Compiler TreePlus
autoQuote' nenv tree =
  case tree of
    (_, TreeLeaf _) ->
      return tree
    (m, TreeNode ts) -> do
      b <- isSpecialForm nenv tree
      let modifier = if b then quoteData else unquoteCode
      ts' <- mapM (autoQuote' nenv) ts
      ts'' <- mapM (modifier nenv) ts'
      return (m, TreeNode ts'')

quoteData :: Map.HashMap T.Text Ident -> TreePlus -> Compiler TreePlus
quoteData nenv tree@(m, _) = do
  b <- isSpecialForm nenv tree
  if b
    then return tree
    else return (m, TreeNode [(m, TreeLeaf "quote"), tree])

unquoteCode :: Map.HashMap T.Text Ident -> TreePlus -> Compiler TreePlus
unquoteCode nenv tree@(m, _) = do
  b <- isSpecialForm nenv tree
  if b
    then return (m, TreeNode [(m, TreeLeaf "unquote"), tree])
    else return tree

isSpecialForm :: Map.HashMap T.Text Ident -> TreePlus -> Compiler Bool
isSpecialForm nenv tree = do
  case tree of
    (m, TreeLeaf x) -> do
      my <- resolveSymbol m (asMetaVar m nenv) x
      case my of
        Just _ ->
          return True
        _ ->
          return False
    (_, TreeNode (leaf@(_, TreeLeaf _) : _)) ->
      isSpecialForm nenv leaf
    _ ->
      return False

generateLastStmtList :: T.Text -> (Env -> [T.Text]) -> Compiler [TreePlus]
generateLastStmtList atom accessor = do
  path <- getCurrentFilePath
  env <- gets accessor
  let m = newHint 0 0 path
  return $ map (\x -> (m, TreeNode [(m, TreeLeaf atom), (m, TreeLeaf x)])) env

generateUnuseStmtList :: Compiler [TreePlus]
generateUnuseStmtList =
  generateLastStmtList "unuse" prefixEnv

generateEndStmtList :: Compiler [TreePlus]
generateEndStmtList =
  generateLastStmtList "end" sectionEnv

generateRemovePrefixStmtList :: Compiler [TreePlus]
generateRemovePrefixStmtList = do
  path <- getCurrentFilePath
  let m = newHint 0 0 path
  nenv <- gets nsEnv
  return $ map (\(from, to) -> (m, TreeNode [(m, TreeLeaf "remove-prefix"), (m, TreeLeaf from), (m, TreeLeaf to)])) nenv
