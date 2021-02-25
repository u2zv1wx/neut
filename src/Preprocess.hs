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
  -- forM_ out' $ \k -> do
  --   p $ T.unpack $ showAsSExp k
  -- p "quitting."
  -- _ <- liftIO $ exitWith ExitSuccess
  modify (\env -> env {enumEnv = Map.empty})
  modify (\env -> env {revEnumEnv = Map.empty})
  return out'

visit :: Path Abs File -> WithEnv [MetaTermPlus]
visit path = do
  pushTrace path
  modify (\env -> env {fileEnv = Map.insert path VisitInfoActive (fileEnv env)})
  modify (\env -> env {phase = 1 + phase env})
  content <- liftIO $ TIO.readFile $ toFilePath path
  tokenize content >>= preprocess'

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

preprocess' :: [TreePlus] -> WithEnv [MetaTermPlus]
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

preprocess'' :: [TreePlus] -> [TreePlus] -> WithEnv [MetaTermPlus]
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
            -- fixme: 定義済みのものがみつかったらエラーにしたほうがいい。
            "let-meta"
              | [(_, TreeLeaf name), body] <- rest -> do
                body' <- evaluate body
                name' <- newNameWith $ asIdent name
                modify (\env -> env {topMetaNameEnv = Map.insert name name' (topMetaNameEnv env)})
                modify (\env -> env {metaTermCtx = IntMap.insert (asInt name') body' (metaTermCtx env)})
                preprocess'' quotedRestStmtList restStmtList
              | otherwise -> do
                raiseSyntaxError m "(let-meta LEAF TREE)"
            "statement-meta" ->
              preprocess'' (rest ++ quotedRestStmtList) restStmtList
            _ ->
              preprocessAux headStmt quotedRestStmtList restStmtList
        _ ->
          preprocessAux headStmt quotedRestStmtList restStmtList

preprocessAux :: TreePlus -> [TreePlus] -> [TreePlus] -> WithEnv [MetaTermPlus]
preprocessAux headStmt expandedRestStmtList restStmtList = do
  headStmt' <- evaluate headStmt
  if isSpecialMetaForm headStmt'
    then preprocess'' (toTree headStmt' : expandedRestStmtList) restStmtList
    else do
      treeList <- preprocess'' expandedRestStmtList restStmtList
      return $ headStmt' : treeList

evaluate :: TreePlus -> WithEnv MetaTermPlus
evaluate e = do
  ctx <- gets metaTermCtx
  interpretCode e >>= discernMetaTerm >>= return . substMetaTerm ctx >>= reduceMetaTerm

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
  WithEnv [MetaTermPlus]
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
      -- p' term
      raiseError m $ "meta-computation resulted in a non-quoted term: " <> showAsSExp (toTree term)

metaToTree :: MetaTermPlus -> WithEnv TreePlus
metaToTree term =
  case term of
    (m, MetaTermLeaf x) ->
      return (m, TreeLeaf x)
    (m, MetaTermNode es) -> do
      es' <- mapM metaToTree es
      return (m, TreeNode es')
    (m, _) -> do
      p' term
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

reduceMetaTerm :: MetaTermPlus -> WithEnv MetaTermPlus
reduceMetaTerm term =
  case term of
    (m, MetaTermImpElim e es) -> do
      e' <- reduceMetaTerm e
      es' <- mapM (reduceMetaTerm) es
      case e' of
        (mLam, MetaTermImpIntro xs mRest body) -> do
          h <- newNameWith' "SELF"
          reduceFix (mLam, MetaTermFix h xs mRest body) es'
        (_, MetaTermFix {}) ->
          reduceFix e' es'
        (_, MetaTermConst c) ->
          reduceConstApp m c es'
        _ -> do
          raiseError m $ "the term \n  " <> showAsSExp (toTree e') <> "\ncannot be applied to:\n  " <> T.intercalate "\n" (map (showAsSExp . toTree) es')
    (m, MetaTermEnumElim (e, _) caseList) -> do
      e' <- reduceMetaTerm e
      let caseList' = map (\(c, body) -> (snd c, body)) caseList
      case e' of
        (_, MetaTermEnumIntro l) ->
          case lookup (EnumCaseLabel l) caseList' of
            Just body ->
              reduceMetaTerm body
            Nothing ->
              raiseError m "found an ill-typed switch"
        _ -> do
          raiseError m "found an ill-typed switch"
    (m, MetaTermNode es) -> do
      es' <- mapM (reduceMetaTerm) es
      return (m, MetaTermNode es')
    _ -> do
      return term

reduceFix :: MetaTermPlus -> [MetaTermPlus] -> WithEnv MetaTermPlus
reduceFix e es =
  case e of
    (m, MetaTermFix f xs mRest body)
      | Just rest <- mRest -> do
        if length xs > length es
          then raiseError m "arity mismatch"
          else do
            let es1 = take (length xs) es
            -- let es2 = map (\x -> (m, MetaTermNecElim x)) $ drop (length xs) es
            let restArg = (m, MetaTermNode (drop (length xs) es))
            -- let restArg = (m, MetaTermNecIntro (m, MetaTermNode es2))
            let sub = IntMap.fromList $ (asInt f, e) : zip (map asInt xs) es1 ++ [(asInt rest, restArg)]
            reduceMetaTerm $ substMetaTerm sub body
      | otherwise -> do
        if length xs /= length es
          then raiseError m "arity mismatch"
          else do
            let sub = IntMap.fromList $ (asInt f, e) : zip (map asInt xs) es
            reduceMetaTerm $ substMetaTerm sub body
    _ ->
      raiseCritical (fst e) "unreachable"

reduceConstApp :: Hint -> T.Text -> [MetaTermPlus] -> WithEnv MetaTermPlus
reduceConstApp m c es =
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
        arg' <- metaToTree arg
        evaluate arg'
    "head"
      | [(_, MetaTermNode (h : _))] <- es ->
        return h
    "is-nil"
      | [(_, MetaTermNode ts)] <- es ->
        return $ liftBool (null ts) m
    "is-leaf"
      | [(_, MetaTermLeaf _)] <- es ->
        return $ liftBool True m
      | [(_, MetaTermNode _)] <- es ->
        return $ liftBool False m
    "is-node"
      | [(_, MetaTermLeaf _)] <- es ->
        return $ liftBool False m
      | [(_, MetaTermNode _)] <- es ->
        return $ liftBool True m
    "leaf-mul"
      | [(mLeaf, MetaTermLeaf s1), (_, MetaTermLeaf s2)] <- es ->
        return (mLeaf, MetaTermLeaf (s1 <> s2))
    "leaf-equal"
      | [(_, MetaTermLeaf s1), (_, MetaTermLeaf s2)] <- es ->
        return $ liftBool (s1 == s2) m
    "leaf-uncons"
      | [(_, MetaTermLeaf s)] <- es -> do
        case T.uncons s of
          Just (ch, rest) ->
            return (m, MetaTermNode [(m, MetaTermLeaf (T.singleton ch)), (m, MetaTermLeaf rest)])
          Nothing ->
            undefined
    "tail"
      | [(mNode, MetaTermNode (_ : rest))] <- es ->
        return (mNode, MetaTermNode rest)
    "new-symbol"
      | [] <- es -> do
        i <- newCount
        return (m, MetaTermLeaf ("#" <> T.pack (show i)))
    "nth"
      | [(_, MetaTermInt64 i), (_, MetaTermNode ts)] <- es -> do
        if 0 <= i && i < fromIntegral (length ts)
          then return $ ts !! (fromIntegral i)
          else raiseError m "index out of range"
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
      Just (>)
    "int-ge" ->
      Just (>=)
    "int-lt" ->
      Just (<)
    "int-le" ->
      Just (<=)
    "int-eq" ->
      Just (==)
    _ ->
      Nothing

liftBool :: Bool -> Hint -> MetaTermPlus
liftBool b m =
  if b
    then (m, MetaTermEnumIntro "bool.true")
    else (m, MetaTermEnumIntro "bool.false")

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
      if isSpecialMetaForm $ embed tree
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
