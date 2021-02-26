module Preprocess (preprocess) where

import Control.Monad.State.Lazy hiding (get)
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Hint
import Data.Ident
import qualified Data.IntMap as IntMap
import Data.List (find)
import Data.Log
import Data.MetaTerm
import Data.Namespace
import Data.Platform
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
  return out

visit :: Path Abs File -> WithEnv [TreePlus]
visit path = do
  pushTrace path
  modify (\env -> env {fileEnv = Map.insert path VisitInfoActive (fileEnv env)})
  modify (\env -> env {phase = 1 + phase env})
  content <- liftIO $ TIO.readFile $ toFilePath path
  tokenize content >>= preprocess'

leave :: WithEnv [TreePlus]
leave = do
  path <- getCurrentFilePath
  popTrace
  modify (\env -> env {fileEnv = Map.insert path VisitInfoFinish (fileEnv env)})
  penv <- gets prefixEnv
  senv <- gets sectionEnv
  let m = newHint 0 0 0 path
  let ts1 = map (\x -> (m, TreeNode [(m, TreeLeaf "unuse"), (m, TreeLeaf x)])) penv
  let ts2 = map (\x -> (m, TreeNode [(m, TreeLeaf "end"), (m, TreeLeaf x)])) senv
  modify (\env -> env {prefixEnv = []})
  modify (\env -> env {sectionEnv = []})
  -- fixme: ここでend/unuseを適切に入れる
  return $ ts1 ++ ts2

pushTrace :: Path Abs File -> WithEnv ()
pushTrace path =
  modify (\env -> env {traceEnv = path : traceEnv env})

popTrace :: WithEnv ()
popTrace =
  modify (\env -> env {traceEnv = tail (traceEnv env)})

preprocess' :: [TreePlus] -> WithEnv [TreePlus]
preprocess' stmtList = do
  case stmtList of
    [] -> do
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
                name' <- newNameWith $ asIdent name
                modify (\env -> env {topMetaNameEnv = Map.insert name name' (topMetaNameEnv env)})
                modify (\env -> env {metaTermCtx = IntMap.insert (asInt name') body' (metaTermCtx env)})
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
            "declare-enum"
              | (_, TreeLeaf name) : ts <- rest -> do
                xis <- interpretEnumItem m name ts
                insEnumEnv m name xis
                preprocess' restStmtList
              | otherwise ->
                raiseSyntaxError m "(declare-enum LEAF TREE ... TREE)"
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
            _ ->
              preprocessAux headStmt restStmtList
        _ ->
          preprocessAux headStmt restStmtList

preprocessAux :: TreePlus -> [TreePlus] -> WithEnv [TreePlus]
preprocessAux headStmt restStmtList = do
  headStmt' <- autoQuote headStmt >>= evaluate >>= specialize
  treeList <- preprocess' restStmtList
  return $ headStmt' : treeList

evaluate :: TreePlus -> WithEnv MetaTermPlus
evaluate e = do
  ctx <- gets metaTermCtx
  interpretCode e >>= discernMetaTerm >>= return . substMetaTerm ctx >>= reduceMetaTerm

includeFile ::
  Hint ->
  Hint ->
  T.Text ->
  [TreePlus] ->
  WithEnv [TreePlus]
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

ensureEnvSanity :: Hint -> WithEnv ()
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

autoQuote :: TreePlus -> WithEnv TreePlus
autoQuote tree = do
  nenv <- gets topMetaNameEnv
  return $ autoQuote' nenv tree

autoQuote' :: Map.HashMap T.Text Ident -> TreePlus -> TreePlus
autoQuote' nenv tree =
  case tree of
    (_, TreeLeaf _) ->
      tree
    (m, TreeNode ts) -> do
      let modifier = if isSpecialForm nenv tree then quoteData else unquoteCode
      let ts' = map (modifier nenv . autoQuote' nenv) ts
      (m, TreeNode ts')

quoteData :: Map.HashMap T.Text Ident -> TreePlus -> TreePlus
quoteData nenv tree@(m, _) =
  if isSpecialForm nenv tree
    then tree
    else (m, TreeNode [(m, TreeLeaf "quasiquote"), tree])

unquoteCode :: Map.HashMap T.Text Ident -> TreePlus -> TreePlus
unquoteCode nenv tree@(m, _) =
  if isSpecialForm nenv tree
    then (m, TreeNode [(m, TreeLeaf "quasiunquote"), tree])
    else tree

isSpecialForm :: Map.HashMap T.Text Ident -> TreePlus -> Bool
isSpecialForm nenv tree =
  case tree of
    (_, TreeLeaf x) ->
      Map.member x nenv
    (_, TreeNode ((_, TreeLeaf x) : _)) ->
      Map.member x nenv
    _ ->
      False

insEnumEnv :: Hint -> T.Text -> [(T.Text, Int)] -> WithEnv ()
insEnumEnv m name xis = do
  eenv <- gets enumEnv
  let definedEnums = Map.keys eenv ++ map fst (concat (Map.elems eenv))
  case find (`elem` definedEnums) $ name : map fst xis of
    Just x ->
      raiseError m $ "the constant `" <> x <> "` is already defined [ENUM]"
    _ -> do
      let (xs, is) = unzip xis
      let rev = Map.fromList $ zip xs (zip (repeat name) is)
      modify
        ( \e ->
            e
              { enumEnv = Map.insert name xis (enumEnv e),
                revEnumEnv = rev `Map.union` revEnumEnv e
              }
        )
