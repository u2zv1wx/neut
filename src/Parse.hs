module Parse
  ( parse,
  )
where

import Control.Monad.State.Lazy hiding (get)
import Data.Code
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Hint
import Data.Ident
-- import qualified Data.IntMap as IntMap
-- import Data.MetaCalc
import Data.Namespace
import Data.Platform
-- import qualified Data.Set as S
import qualified Data.Text as T
-- import qualified Data.Text.IO as TIO
import Data.Tree
import Data.WeakTerm
-- import GHC.IO.Handle
import Parse.Discern
import Parse.Interpret
import Parse.Rule

-- import Parse.Tokenize
-- import Path
-- import Path.IO
-- import Reduce.MetaCalc
-- import System.Exit
-- import System.Process hiding (env)
-- import Text.Read (readMaybe)

parse :: [TreePlus] -> WithEnv [WeakStmt]
parse treeList =
  parse' Map.empty treeList

-- parse :: Path Abs File -> WithEnv [WeakStmt]
-- parse inputPath = do
--   stmtList <- visit inputPath
--   pushTrace inputPath
--   parse' Map.empty stmtList

parse' :: SubstCode -> [TreePlus] -> WithEnv [WeakStmt]
parse' sub stmtTreeList =
  case stmtTreeList of
    [] ->
      return []
    headStmt : restStmtList -> do
      case headStmt of
        (m, TreeNode (leaf@(_, TreeLeaf headAtom) : rest)) ->
          case headAtom of
            "constant"
              | [(_, TreeLeaf name), t] <- rest -> do
                t' <- interpret t >>= discern
                name' <- withSectionPrefix name
                insertConstant m name'
                defList <- parse' sub restStmtList
                return $ WeakStmtConstDecl (m, name', t') : defList
              | otherwise ->
                raiseSyntaxError m "(constant LEAF TREE)"
            "end"
              | [(_, TreeLeaf s)] <- rest -> do
                ns <- gets sectionEnv
                case ns of
                  [] ->
                    raiseError m "there is no section to end"
                  s' : ns'
                    | s == s' -> do
                      getCurrentSection >>= unuse
                      modify (\e -> e {sectionEnv = ns'})
                      parse' sub restStmtList
                    | otherwise ->
                      raiseError m $
                        "the innermost section is not `" <> s <> "`, but is `" <> s' <> "`"
              | otherwise ->
                raiseSyntaxError m "(end LEAF)"
            "enum"
              | (_, TreeLeaf name) : ts <- rest -> do
                xis <- interpretEnumItem m name ts
                insEnumEnv m name xis
                parse' sub restStmtList
              | otherwise ->
                raiseSyntaxError m "(enum LEAF TREE ... TREE)"
            "erase"
              | [(ms, TreeLeaf s)] <- rest -> do
                nenv <- gets topNameEnv
                s' <- asText <$> discernText ms s
                modify (\env -> env {topNameEnv = Map.filterWithKey (\k _ -> k /= s') nenv})
                parse' sub restStmtList
              | otherwise ->
                raiseSyntaxError m "(erase LEAF)"
            "data"
              | name@(mFun, TreeLeaf _) : xts@(_, TreeNode _) : es' <- rest ->
                parse' sub $ (m, TreeNode [leaf, (mFun, TreeNode (name : xts : es'))]) : restStmtList
              | otherwise -> do
                stmtList1 <- parseData m rest
                stmtList2 <- parse' sub restStmtList
                return $ stmtList1 ++ stmtList2
            "introspect"
              | ((mx, TreeLeaf x) : stmtClauseList) <- rest -> do
                val <- retrieveCompileTimeVarValue mx x
                stmtClauseList' <- mapM parseStmtClause stmtClauseList
                case lookup val stmtClauseList' of
                  Nothing ->
                    parse' sub restStmtList
                  Just as1 ->
                    parse' sub $ as1 ++ restStmtList
              | otherwise ->
                raiseSyntaxError m "(introspect LEAF TREE*)"
            "let"
              | [(mx, TreeLeaf x), t, e] <- rest -> do
                let xt = (mx, TreeNode [(mx, TreeLeaf x), t])
                parse' sub ((m, TreeNode [(m, TreeLeaf "let"), xt, e]) : restStmtList)
              | [xt, e] <- rest -> do
                e' <- interpret e >>= discern
                xt' <- prefixTextPlus xt >>= interpretIdentPlus >>= discernIdentPlus
                defList <- parse' sub restStmtList
                return $ WeakStmtLet m xt' e' : defList
              | otherwise ->
                raiseSyntaxError m "(let LEAF TREE TREE) | (let TREE TREE)"
            "record"
              | (_, TreeLeaf _) : (_, TreeNode _) : _ <- rest -> do
                rest' <- asData m rest
                stmtList1 <- parseData m [rest']
                stmtList2 <- generateProjections rest'
                stmtList3 <- parse' sub restStmtList
                return $ stmtList1 ++ stmtList2 ++ stmtList3
              | otherwise ->
                raiseSyntaxError m "(record name (TREE ... TREE) TREE ... TREE)"
            "section"
              | [(_, TreeLeaf s)] <- rest -> do
                modify (\e -> e {sectionEnv = s : sectionEnv e})
                getCurrentSection >>= use
                parse' sub restStmtList
              | otherwise ->
                raiseSyntaxError m "(section LEAF)"
            "use"
              | [(_, TreeLeaf s)] <- rest ->
                use s >> parse' sub restStmtList
              | otherwise ->
                raiseSyntaxError m "(use LEAF)"
            "unuse"
              | [(_, TreeLeaf s)] <- rest ->
                unuse s >> parse' sub restStmtList
              | otherwise ->
                raiseSyntaxError m "(unuse LEAF)"
            _ ->
              interpretAux sub headStmt restStmtList
        _ ->
          interpretAux sub headStmt restStmtList

interpretAux :: SubstCode -> TreePlus -> [TreePlus] -> WithEnv [WeakStmt]
interpretAux sub headStmt restStmtList = do
  e <- interpret headStmt >>= discern
  h <- newNameWith'' "_"
  let m = metaOf e
  t <- newAster m
  defList <- parse' sub restStmtList
  return $ WeakStmtLet m (m, h, t) e : defList

use :: T.Text -> WithEnv ()
use s =
  modify (\e -> e {prefixEnv = s : prefixEnv e})

unuse :: T.Text -> WithEnv ()
unuse s =
  modify (\e -> e {prefixEnv = filter (/= s) (prefixEnv e)})

withSectionPrefix :: T.Text -> WithEnv T.Text
withSectionPrefix x = do
  ns <- gets sectionEnv
  return $ foldl (\acc n -> n <> nsSep <> acc) x ns

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
      getCurrentSection' ns <> nsSep <> n

-- readStrOrThrow :: (Read a) => Hint -> T.Text -> WithEnv a
-- readStrOrThrow m quotedStr =
--   case readMaybe (T.unpack quotedStr) of
--     Nothing ->
--       raiseError m "the atom here must be a string"
--     Just str ->
--       return str

-- ensureEnvSanity :: Hint -> WithEnv ()
-- ensureEnvSanity m = do
--   penv <- gets prefixEnv
--   if null penv
--     then return ()
--     else raiseError m "`include` can only be used with no prefix assumption"

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

parseStmtClause :: TreePlus -> WithEnv (T.Text, [TreePlus])
parseStmtClause tree =
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

-- showCyclicPath :: [Path Abs File] -> T.Text
-- showCyclicPath pathList =
--   case pathList of
--     [] ->
--       ""
--     [path] ->
--       T.pack (toFilePath path)
--     (path : ps) ->
--       "     " <> T.pack (toFilePath path) <> showCyclicPath' ps

-- showCyclicPath' :: [Path Abs File] -> T.Text
-- showCyclicPath' pathList =
--   case pathList of
--     [] ->
--       ""
--     [path] ->
--       "\n  ~> " <> T.pack (toFilePath path)
--     (path : ps) ->
--       "\n  ~> " <> T.pack (toFilePath path) <> showCyclicPath' ps

-- ensureFileExistence :: Hint -> Path Abs File -> WithEnv ()
-- ensureFileExistence m path = do
--   b <- doesFileExist path
--   if b
--     then return ()
--     else raiseError m $ "no such file: " <> T.pack (toFilePath path)

-- raiseIfFailure :: Hint -> String -> ExitCode -> Handle -> Path Abs Dir -> WithEnv ()
-- raiseIfFailure m procName exitCode h pkgDirPath =
--   case exitCode of
--     ExitSuccess ->
--       return ()
--     ExitFailure i -> do
--       removeDir pkgDirPath -- cleanup
--       errStr <- liftIO $ hGetContents h
--       raiseError m $ T.pack $ "the child process `" ++ procName ++ "` failed with the following message (exitcode = " ++ show i ++ "):\n" ++ errStr

-- parseMetaCalc :: [TreePlus] -> WithEnv [TreePlus]
-- parseMetaCalc ts =
--   parseMetaCalc' IntMap.empty ts

-- parseMetaCalc' :: SubstMetaCalc -> [TreePlus] -> WithEnv [TreePlus]
-- parseMetaCalc' sub stmtList =
--   case stmtList of
--     [] ->
--       leave
--     headStmt : restStmtList ->
--       case headStmt of
--         (m, TreeNode ((_, TreeLeaf headAtom) : rest)) ->
--           case headAtom of
--             "denote"
--               | [(_, TreeLeaf name), body] <- rest -> do
--                 body' <- interpretMetaCalc body >>= discernMetaCalc
--                 body'' <- reduceMetaCalc' $ substMetaCalc sub body'
--                 name' <- newNameWith $ asIdent name
--                 modify (\env -> env {topMetaNameEnv = Map.insert name name' (topMetaNameEnv env)})
--                 parseMetaCalc' (IntMap.insert (asInt name') body'' sub) restStmtList
--               | otherwise ->
--                 raiseSyntaxError m "(denote LEAF TREE)"
--             "include"
--               | [(mPath, TreeLeaf pathString)] <- rest,
--                 not (T.null pathString) ->
--                 includeFile sub m mPath pathString restStmtList
--               | otherwise ->
--                 raiseSyntaxError m "(include LEAF)"
--             "ensure"
--               | [(_, TreeLeaf pkg), (mUrl, TreeLeaf urlStr)] <- rest -> do
--                 libDirPath <- getLibraryDirPath
--                 pkg' <- parseRelDir $ T.unpack pkg
--                 let pkgDirPath = libDirPath </> pkg'
--                 isAlreadyInstalled <- doesDirExist pkgDirPath
--                 when (not isAlreadyInstalled) $ do
--                   ensureDir pkgDirPath
--                   urlStr' <- readStrOrThrow mUrl urlStr
--                   let curlCmd = proc "curl" ["-s", "-S", "-L", urlStr']
--                   let tarCmd = proc "tar" ["xJf", "-", "-C", toFilePath pkg', "--strip-components=1"]
--                   (_, Just stdoutHandler, Just curlErrorHandler, curlHandler) <-
--                     liftIO $ createProcess curlCmd {cwd = Just (toFilePath libDirPath), std_out = CreatePipe, std_err = CreatePipe}
--                   (_, _, Just tarErrorHandler, tarHandler) <-
--                     liftIO $ createProcess tarCmd {cwd = Just (toFilePath libDirPath), std_in = UseHandle stdoutHandler, std_err = CreatePipe}
--                   note' $ "downloading " <> pkg <> " from " <> T.pack urlStr'
--                   curlExitCode <- liftIO $ waitForProcess curlHandler
--                   raiseIfFailure mUrl "curl" curlExitCode curlErrorHandler pkgDirPath
--                   note' $ "extracting " <> pkg <> " into " <> T.pack (toFilePath pkgDirPath)
--                   tarExitCode <- liftIO $ waitForProcess tarHandler
--                   raiseIfFailure mUrl "tar" tarExitCode tarErrorHandler pkgDirPath
--                   return ()
--                 parseMetaCalc' sub restStmtList
--               | otherwise ->
--                 raiseSyntaxError m "(ensure LEAF LEAF)"
--             "statement" ->
--               parseMetaCalc' sub $ rest ++ restStmtList
--             _ ->
--               parseMetaCalcAux sub headStmt restStmtList
--         _ ->
--           parseMetaCalcAux sub headStmt restStmtList

-- parseMetaCalcAux :: SubstMetaCalc -> TreePlus -> [TreePlus] -> WithEnv [TreePlus]
-- parseMetaCalcAux sub headStmt restStmtList = do
--   headStmt' <- interpretMetaCalc headStmt >>= discernMetaCalc
--   headStmt'' <- reduceMetaCalc $ substMetaCalc sub headStmt'
--   if isSpecialMetaForm headStmt''
--     then parseMetaCalc' sub $ headStmt'' : restStmtList
--     else do
--       treeList <- parseMetaCalc' sub restStmtList
--       return $ headStmt'' : treeList

-- isSpecialMetaForm :: TreePlus -> Bool
-- isSpecialMetaForm tree =
--   case tree of
--     (_, TreeNode ((_, TreeLeaf x) : _)) ->
--       S.member x metaKeywordSet
--     _ ->
--       False

-- metaKeywordSet :: S.Set T.Text
-- metaKeywordSet =
--   S.fromList
--     [ "denote",
--       "statement",
--       "include",
--       "ensure"
--     ]

-- includeFile ::
--   SubstMetaCalc ->
--   Hint ->
--   Hint ->
--   T.Text ->
--   [TreePlus] ->
--   WithEnv [TreePlus]
-- includeFile sub m mPath pathString as = do
--   ensureEnvSanity m
--   path <- readStrOrThrow mPath pathString
--   when (null path) $ raiseError m "found an empty path"
--   dirPath <-
--     if head path == '.'
--       then getCurrentDirPath
--       else getLibraryDirPath
--   newPath <- resolveFile dirPath path
--   ensureFileExistence m newPath
--   denv <- gets fileEnv
--   case Map.lookup newPath denv of
--     Just VisitInfoActive -> do
--       tenv <- gets traceEnv
--       let cyclicPath = dropWhile (/= newPath) (reverse tenv) ++ [newPath]
--       raiseError m $ "found cyclic inclusion:\n" <> showCyclicPath cyclicPath
--     Just VisitInfoFinish ->
--       parseMetaCalc' sub as
--     Nothing -> do
--       treeList1 <- visit newPath
--       treeList2 <- parseMetaCalc' sub as
--       return $ treeList1 ++ treeList2

-- visit :: Path Abs File -> WithEnv [TreePlus]
-- visit path = do
--   pushTrace path
--   modify (\env -> env {fileEnv = Map.insert path VisitInfoActive (fileEnv env)})
--   modify (\env -> env {phase = 1 + phase env})
--   content <- liftIO $ TIO.readFile $ toFilePath path
--   tokenize content >>= parseMetaCalc

-- leave :: WithEnv [TreePlus]
-- leave = do
--   path <- getCurrentFilePath
--   popTrace
--   modify (\env -> env {fileEnv = Map.insert path VisitInfoFinish (fileEnv env)})
--   modify (\env -> env {prefixEnv = []})
--   modify (\env -> env {sectionEnv = []})
--   return []

-- pushTrace :: Path Abs File -> WithEnv ()
-- pushTrace path =
--   modify (\env -> env {traceEnv = path : traceEnv env})

-- popTrace :: WithEnv ()
-- popTrace =
--   modify (\env -> env {traceEnv = tail (traceEnv env)})
