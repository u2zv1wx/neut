module Preprocess (preprocess) where

import Control.Monad.State.Lazy hiding (get)
import Data.EnumCase
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Hint
import Data.Ident
import Data.Int
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
preprocess' ctx stmtList = do
  case stmtList of
    [] ->
      leave
    headStmt : restStmtList -> do
      case headStmt of
        (m, TreeNode ((_, TreeLeaf headAtom) : rest)) ->
          case headAtom of
            "auto-quote"
              | [(_, TreeLeaf name)] <- rest -> do
                modify (\env -> env {autoQuoteEnv = S.insert name (autoQuoteEnv env)})
                preprocess' ctx restStmtList
              | otherwise ->
                raiseSyntaxError m "(auto-quote LEAF)"
            "let"
              | [(_, TreeLeaf name), body] <- rest -> do
                body' <- evaluate ctx body
                name' <- newNameWith $ asIdent name
                modify (\env -> env {topMetaNameEnv = Map.insert name name' (topMetaNameEnv env)})
                preprocess' (IntMap.insert (asInt name') body' ctx) restStmtList
              | otherwise -> do
                raiseSyntaxError m "(let LEAF TREE)"
            "literal" -> do
              rest' <- mapM (evaluate ctx . unwrap) rest
              treeList <- preprocess' ctx restStmtList
              return $ rest' ++ treeList
            "enum"
              | (_, TreeLeaf name) : ts <- rest -> do
                xis <- interpretEnumItem m name ts
                insEnumEnv m name xis
                preprocess' ctx restStmtList
              | otherwise ->
                raiseSyntaxError m "(enum LEAF TREE ... TREE)"
            "include"
              | [(mPath, TreeLeaf pathString)] <- rest,
                not (T.null pathString) ->
                includeFile ctx m mPath pathString restStmtList
              | otherwise ->
                raiseSyntaxError m "(include LEAF)"
            "introspect"
              | ((mx, TreeLeaf x) : stmtClauseList) <- rest -> do
                val <- retrieveCompileTimeVarValue mx x
                stmtClauseList' <- mapM preprocessStmtClause stmtClauseList
                case lookup val stmtClauseList' of
                  Nothing ->
                    preprocess' ctx restStmtList
                  Just as1 ->
                    preprocess' ctx $ as1 ++ restStmtList
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
                preprocess' ctx restStmtList
              | otherwise ->
                raiseSyntaxError m "(ensure LEAF LEAF)"
            "statement" ->
              preprocess' ctx $ rest ++ restStmtList
            _ ->
              preprocessAux ctx headStmt restStmtList
        _ ->
          preprocessAux ctx headStmt restStmtList

preprocessAux :: SubstMetaTerm -> TreePlus -> [TreePlus] -> WithEnv [MetaTermPlus]
preprocessAux ctx headStmt restStmtList = do
  headStmt' <- evaluate ctx (unwrap headStmt)
  if isSpecialMetaForm headStmt'
    then preprocess' ctx $ toTree headStmt' : restStmtList
    else do
      treeList <- preprocess' ctx restStmtList
      return $ headStmt' : treeList

evaluate :: SubstMetaTerm -> TreePlus -> WithEnv MetaTermPlus
evaluate ctx e = do
  interpretCode e >>= discernMetaTerm >>= return . substMetaTerm ctx >>= reduceMetaTerm ctx

unwrap :: TreePlus -> TreePlus
unwrap t = do
  let m = fst t
  (m, TreeNode [(m, TreeLeaf "apply"), t])

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
    [ "auto-quote",
      "ensure",
      "enum",
      "include",
      "introspect",
      "let",
      "literal",
      "statement"
    ]

includeFile ::
  SubstMetaTerm ->
  Hint ->
  Hint ->
  T.Text ->
  [TreePlus] ->
  WithEnv [MetaTermPlus]
includeFile ctx m mPath pathString as = do
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
      preprocess' ctx as
    Nothing -> do
      treeList1 <- visit newPath
      treeList2 <- preprocess' ctx as
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
      -- p' term
      raiseError m $ "meta-computation resulted in a non-quoted term: " <> showAsSExp (toTree term)

reflect :: MetaTermPlus -> WithEnv TreePlus
reflect term =
  case term of
    (m, MetaTermLeaf x) ->
      return (m, TreeLeaf x)
    (m, MetaTermNode es) -> do
      es' <- mapM reflect es
      return (m, TreeNode es')
    (m, _) -> do
      raiseError m $ "the argument of eval isn't a valid AST " <> showAsSExp (toTree term)

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

reduceMetaTerm :: SubstMetaTerm -> MetaTermPlus -> WithEnv MetaTermPlus
reduceMetaTerm ctx term =
  case term of
    (m, MetaTermImpElim e es) -> do
      e' <- reduceMetaTerm ctx e
      es' <- mapM (reduceMetaTerm ctx) es
      case e' of
        (mLam, MetaTermImpIntro xs mRest body) -> do
          h <- newNameWith' "SELF"
          reduceFix ctx (mLam, MetaTermFix h xs mRest body) es'
        (_, MetaTermFix {}) ->
          reduceFix ctx e' es'
        (_, MetaTermConst c) ->
          reduceConstApp ctx m c es'
        _ -> do
          raiseError m $ "the term \n  " <> showAsSExp (toTree e') <> "\ncannot be applied to:\n  " <> T.intercalate "\n" (map (showAsSExp . toTree) es')
    (m, MetaTermEnumElim (e, _) caseList) -> do
      e' <- reduceMetaTerm ctx e
      let caseList' = map (\(c, body) -> (snd c, body)) caseList
      case e' of
        (_, MetaTermEnumIntro l) ->
          case lookup (EnumCaseLabel l) caseList' of
            Just body ->
              reduceMetaTerm ctx body
            Nothing ->
              raiseError m "found an ill-typed switch"
        _ -> do
          raiseError m "found an ill-typed switch"
    (m, MetaTermNode es) -> do
      es' <- mapM (reduceMetaTerm ctx) es
      return (m, MetaTermNode es')
    _ -> do
      return term

reduceFix :: SubstMetaTerm -> MetaTermPlus -> [MetaTermPlus] -> WithEnv MetaTermPlus
reduceFix ctx e es =
  case e of
    (m, MetaTermFix f xs mRest body)
      | Just rest <- mRest -> do
        if length xs > length es
          then raiseError m "arity mismatch"
          else do
            let es1 = take (length xs) es
            -- let es2 = drop (length xs) es
            -- let es2 = map (\x -> (m, MetaTermNecElim x)) $ drop (length xs) es
            let restArg = (m, MetaTermNode (drop (length xs) es))
            -- let restArg = (m, MetaTermNecIntro (m, MetaTermNode es2))
            let sub = IntMap.fromList $ (asInt f, e) : zip (map asInt xs) es1 ++ [(asInt rest, restArg)]
            reduceMetaTerm ctx $ substMetaTerm sub body
      | otherwise -> do
        if length xs /= length es
          then raiseError m "arity mismatch"
          else do
            let sub = IntMap.fromList $ (asInt f, e) : zip (map asInt xs) es
            reduceMetaTerm ctx $ substMetaTerm sub body
    _ ->
      raiseCritical (fst e) "unreachable"

reduceConstApp :: SubstMetaTerm -> Hint -> T.Text -> [MetaTermPlus] -> WithEnv MetaTermPlus
reduceConstApp ctx m c es =
  case c of
    "cons"
      | [t, (_, MetaTermNode ts)] <- es ->
        return (m, MetaTermNode (t : ts))
    "dump"
      | [arg] <- es -> do
        liftIO $ putStrLn $ T.unpack $ showAsSExp $ toTree arg
        return (m, MetaTermEnumIntro "top.unit")
    "evaluate"
      | [arg] <- es -> do
        arg' <- reduceMetaTerm ctx (m, MetaTermImpElim arg []) >>= reflect
        evaluate ctx arg'
    "head"
      | [(_, MetaTermNode (h : _))] <- es ->
        return h
    "is-nil"
      | [(_, MetaTermNode ts)] <- es ->
        return $ liftBool (null ts) m
    "leaf-mul"
      | [(mLeaf, MetaTermLeaf s1), (_, MetaTermLeaf s2)] <- es ->
        return (mLeaf, MetaTermLeaf (s1 <> s2))
    "leaf-equal"
      | [(_, MetaTermLeaf s1), (_, MetaTermLeaf s2)] <- es ->
        return $ liftBool (s1 == s2) m
    "tail"
      | [(mNode, MetaTermNode (_ : rest))] <- es ->
        return (mNode, MetaTermNode rest)
    _
      | Just op <- toArithOp c,
        [(_, MetaTermInt64 i1), (_, MetaTermInt64 i2)] <- es ->
        return (m, MetaTermInt64 (op i1 i2))
      | Just op <- toCmpOp c,
        [(_, MetaTermInt64 i1), (_, MetaTermInt64 i2)] <- es ->
        return $ liftBool (op i1 i2) m
      | otherwise -> do
        let textList = map (showAsSExp . toTree) es
        raiseError m $ "the constant `" <> c <> "` cannot be used with the following arguments:\n" <> T.intercalate "\n" textList

toArithOp :: T.Text -> Maybe (Int64 -> Int64 -> Int64)
toArithOp opStr =
  case opStr of
    "int-add" ->
      Just (+)
    "int-sub" ->
      Just (-)
    "int-mul" ->
      Just (*)
    "int-div" ->
      Just div
    _ ->
      Nothing

toCmpOp :: T.Text -> Maybe (Int64 -> Int64 -> Bool)
toCmpOp opStr =
  case opStr of
    "int-gt" ->
      Just (<)
    "int-ge" ->
      Just (<=)
    "int-lt" ->
      Just (>)
    "int-le" ->
      Just (>=)
    "int-eq" ->
      Just (==)
    _ ->
      Nothing

liftBool :: Bool -> Hint -> MetaTermPlus
liftBool b m =
  if b
    then (m, MetaTermEnumIntro "bool.true")
    else (m, MetaTermEnumIntro "bool.false")
