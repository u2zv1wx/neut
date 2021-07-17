module Parse
  ( parse,
  )
where

import Control.Monad (forM_, when)
import Data.Basic
import Data.Global
import qualified Data.HashMap.Lazy as Map
import Data.IORef
import Data.List (find)
import Data.Log
import Data.Namespace
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.WeakTerm
import GHC.IO.Handle
import Parse.Core
import Parse.Discern
import Parse.WeakTerm
import Path
import Path.IO
import System.Exit
import System.Process hiding (env)

--
-- core functions
--

parse :: Path Abs File -> IO [WeakStmtPlus]
parse path = do
  pushTrace path
  result <- visit path
  -- ensureMain
  return result

-- ensureMain :: IO ()
-- ensureMain = do
--   m <- currentHint
--   _ <- discern (m, WeakTermVar VarKindLocal $ asIdent "main")
--   return ()

-- when (Map.member (asText x) nenv) $
--   raiseError m $ "the variable `" <> asText x <> "` is already defined at the top level"

visit :: Path Abs File -> IO [WeakStmtPlus]
visit path = do
  -- fixme: ここでpathがdouble quoteを含んでいないことをチェック
  pushTrace path
  ensureNoDoubleQuotes path
  modifyIORef' fileEnv $ \env -> Map.insert path VisitInfoActive env
  withNestedState $ do
    TIO.readFile (toFilePath path) >>= initializeState
    skip
    headerOrStmt path

ensureNoDoubleQuotes :: Path Abs File -> IO ()
ensureNoDoubleQuotes path = do
  m <- currentHint
  if ('\'' `elem` toFilePath path)
    then raiseError m "filepath cannot contain double quotes"
    else return ()

leave :: IO [WeakStmt]
leave = do
  path <- getCurrentFilePath
  modifyIORef' fileEnv $ \env -> Map.insert path VisitInfoFinish env
  popTrace
  return []

pushTrace :: Path Abs File -> IO ()
pushTrace path =
  modifyIORef' traceEnv $ \env -> path : env

popTrace :: IO ()
popTrace =
  modifyIORef' traceEnv $ \env -> tail env

headerOrStmt :: Path Abs File -> IO [WeakStmtPlus]
headerOrStmt path = do
  s <- readIORef text
  if T.null s
    then leave >>= \result -> return [(path, result)]
    else do
      headSymbol <- lookAhead (symbolMaybe isSymbolChar)
      case headSymbol of
        Just "include" -> do
          defList1 <- stmtInclude
          defList2 <- headerOrStmt path
          return $ defList1 ++ defList2
        Just "ensure" -> do
          stmtEnsure
          headerOrStmt path
        _ -> do
          stmtList <- stmt >>= discernStmtList
          return [(path, stmtList)]

stmt :: IO [WeakStmt]
stmt = do
  s <- readIORef text
  if T.null s
    then leave
    else do
      headSymbol <- lookAhead (symbolMaybe isSymbolChar)
      case headSymbol of
        Just "define" -> do
          def <- stmtDefine True
          stmtList <- stmt
          return $ def : stmtList
        Just "define-opaque" -> do
          def <- stmtDefine False
          stmtList <- stmt
          return $ def : stmtList
        Just "define-enum" -> do
          stmtDefineEnum
          stmt
        Just "include" -> do
          m <- currentHint
          raiseParseError m "`include` can only be used at the header section of a file"
        Just "ensure" -> do
          m <- currentHint
          raiseParseError m "`ensure` can only be used at the header section of a file"
        Just "define-data" -> do
          stmtList1 <- stmtDefineData
          stmtList2 <- stmt
          return $ stmtList1 ++ stmtList2
        Just "define-codata" -> do
          stmtList1 <- stmtDefineCodata
          stmtList2 <- stmt
          return $ stmtList1 ++ stmtList2
        Just "define-resource-type" -> do
          def <- stmtDefineResourceType
          stmtList <- stmt
          return $ def : stmtList
        Just "section" -> do
          st <- stmtSection
          stmtList <- stmt
          return $ st : stmtList
        Just "end" -> do
          st <- stmtEnd
          stmtList <- stmt
          return $ st : stmtList
        Just "define-prefix" -> do
          st <- stmtDefinePrefix
          stmtList <- stmt
          return $ st : stmtList
        Just "remove-prefix" -> do
          st <- stmtRemovePrefix
          stmtList <- stmt
          return $ st : stmtList
        Just "use" -> do
          st <- stmtUse
          stmtList <- stmt
          return $ st : stmtList
        Just "unuse" -> do
          st <- stmtUnuse
          stmtList <- stmt
          return $ st : stmtList
        Just x -> do
          m <- currentHint
          raiseParseError m $ "invalid statement: " <> x
        Nothing -> do
          m <- currentHint
          raiseParseError m $ "found the empty symbol when expecting a statement"

--
-- parser for statements
--

-- define name (x1 : A1) ... (xn : An) : A = e
stmtDefine :: Bool -> IO WeakStmt
stmtDefine isReducible = do
  m <- currentHint
  if isReducible
    then token "define"
    else token "define-opaque"
  (mFun, funName) <- var
  funName' <- withSectionPrefix funName
  argList <- many weakIdentPlus
  token ":"
  codType <- weakTerm
  token "="
  e <- weakTerm
  case argList of
    [] ->
      defineTerm isReducible m funName' codType e
    _ ->
      defineFunction isReducible m mFun funName' argList codType e

defineFunction :: IsReducible -> Hint -> Hint -> T.Text -> [WeakIdentPlus] -> WeakTermPlus -> WeakTermPlus -> IO WeakStmt
defineFunction isReducible m mFun funName' argList codType e = do
  let piType = (m, WeakTermPi argList codType)
  funName'' <- discernTopLevelName isReducible m $ asIdent funName'
  let e' = (m, WeakTermPiIntro OpacityTranslucent (LamKindFix (mFun, asIdent funName', piType)) argList e)
  return $ WeakStmtDef m funName'' piType e'

defineTerm :: IsReducible -> Hint -> T.Text -> WeakTermPlus -> WeakTermPlus -> IO WeakStmt
defineTerm isReducible m funName' codType e = do
  funName'' <- discernTopLevelName isReducible m $ asIdent funName'
  return $ WeakStmtDef m funName'' codType e

stmtDefineEnum :: IO ()
stmtDefineEnum = do
  m <- currentHint
  token "define-enum"
  name <- varText >>= withSectionPrefix
  itemList <- many stmtDefineEnumClause
  let itemList' = arrangeEnumItemList name 0 itemList
  when (not (isLinear (map snd itemList'))) $
    raiseError m "found a collision of discriminant"
  insEnumEnv m name itemList'

arrangeEnumItemList :: T.Text -> Int -> [(T.Text, Maybe Int)] -> [(T.Text, Int)]
arrangeEnumItemList name currentValue clauseList =
  case clauseList of
    [] ->
      []
    (item, Nothing) : rest ->
      (name <> nsSep <> item, currentValue) : arrangeEnumItemList name (currentValue + 1) rest
    (item, Just v) : rest ->
      (name <> nsSep <> item, v) : arrangeEnumItemList name (v + 1) rest

stmtDefineEnumClause :: IO (T.Text, Maybe Int)
stmtDefineEnumClause = do
  tryPlanList
    [ stmtDefineEnumClauseWithDiscriminant,
      stmtDefineEnumClauseWithoutDiscriminant
    ]

stmtDefineEnumClauseWithDiscriminant :: IO (T.Text, Maybe Int)
stmtDefineEnumClauseWithDiscriminant = do
  token "-"
  item <- varText
  token "<-"
  discriminant <- integer
  return (item, Just (fromInteger discriminant))

stmtDefineEnumClauseWithoutDiscriminant :: IO (T.Text, Maybe Int)
stmtDefineEnumClauseWithoutDiscriminant = do
  token "-"
  item <- varText
  return (item, Nothing)

stmtEnsure :: IO ()
stmtEnsure = do
  token "ensure"
  pkgStr <- symbol
  mUrl <- currentHint
  urlStr <- string
  libDirPath <- getLibraryDirPath
  pkgStr' <- parseRelDir $ T.unpack pkgStr
  let pkgStrDirPath = libDirPath </> pkgStr'
  isAlreadyInstalled <- doesDirExist pkgStrDirPath
  when (not isAlreadyInstalled) $ do
    ensureDir pkgStrDirPath
    let urlStr' = T.unpack urlStr
    p urlStr'
    let curlCmd = proc "curl" ["-s", "-S", "-L", urlStr']
    let tarCmd = proc "tar" ["xJf", "-", "-C", toFilePath pkgStr', "--strip-components=1"]
    (_, Just stdoutHandler, Just curlErrorHandler, curlHandler) <-
      createProcess curlCmd {cwd = Just (toFilePath libDirPath), std_out = CreatePipe, std_err = CreatePipe}
    (_, _, Just tarErrorHandler, tarHandler) <-
      createProcess tarCmd {cwd = Just (toFilePath libDirPath), std_in = UseHandle stdoutHandler, std_err = CreatePipe}
    note' $ "downloading " <> pkgStr <> " from " <> T.pack urlStr'
    curlExitCode <- waitForProcess curlHandler
    raiseIfFailure mUrl "curl" curlExitCode curlErrorHandler pkgStrDirPath
    note' $ "extracting " <> pkgStr <> " into " <> T.pack (toFilePath pkgStrDirPath)
    tarExitCode <- waitForProcess tarHandler
    raiseIfFailure mUrl "tar" tarExitCode tarErrorHandler pkgStrDirPath

raiseIfFailure :: Hint -> String -> ExitCode -> Handle -> Path Abs Dir -> IO ()
raiseIfFailure m procName exitCode h pkgDirPath =
  case exitCode of
    ExitSuccess ->
      return ()
    ExitFailure i -> do
      removeDir pkgDirPath
      errStr <- hGetContents h
      raiseError m $ T.pack $ "the child process `" ++ procName ++ "` failed with the following message (exitcode = " ++ show i ++ "):\n" ++ errStr

stmtSection :: IO WeakStmt
stmtSection = do
  token "section"
  name <- varText
  handleSection name
  return $ WeakStmtUse name

stmtEnd :: IO WeakStmt
stmtEnd = do
  m <- currentHint
  token "end"
  name <- varText
  handleEnd m name
  return $ WeakStmtUnuse name

stmtUse :: IO WeakStmt
stmtUse = do
  token "use"
  name <- varText
  return $ WeakStmtUse name

stmtUnuse :: IO WeakStmt
stmtUnuse = do
  token "unuse"
  name <- varText
  return $ WeakStmtUnuse name

stmtDefinePrefix :: IO WeakStmt
stmtDefinePrefix = do
  token "define-prefix"
  from <- varText
  token "="
  to <- varText
  return $ WeakStmtDefinePrefix from to

stmtRemovePrefix :: IO WeakStmt
stmtRemovePrefix = do
  token "remove-prefix"
  from <- varText
  token "="
  to <- varText
  return $ WeakStmtRemovePrefix from to

stmtInclude :: IO [WeakStmtPlus]
stmtInclude = do
  m <- currentHint
  token "include"
  path <- T.unpack <$> string
  dirPath <-
    if head path == '.'
      then getCurrentDirPath
      else getLibraryDirPath
  newPath <- resolveFile dirPath path
  ensureFileExistence m newPath
  denv <- readIORef fileEnv
  case Map.lookup newPath denv of
    Just VisitInfoActive -> do
      tenv <- readIORef traceEnv
      let cyclicPath = dropWhile (/= newPath) (reverse tenv) ++ [newPath]
      raiseError m $ "found a cyclic inclusion:\n" <> showCyclicPath cyclicPath
    Just VisitInfoFinish ->
      return []
    Nothing ->
      visit newPath

ensureFileExistence :: Hint -> Path Abs File -> IO ()
ensureFileExistence m path = do
  b <- doesFileExist path
  if b
    then return ()
    else raiseError m $ "no such file: " <> T.pack (toFilePath path)

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

stmtDefineData :: IO [WeakStmt]
stmtDefineData = do
  m <- currentHint
  token "define-data"
  mFun <- currentHint
  a <- varText >>= withSectionPrefix
  xts <- many weakAscription
  bts <- many stmtDefineDataClause
  defineData m mFun a xts bts

defineData :: Hint -> Hint -> T.Text -> [WeakIdentPlus] -> [(Hint, T.Text, [WeakIdentPlus])] -> IO [WeakStmt]
defineData m mFun a xts bts = do
  setAsData a (length xts) bts
  z <- newTextualIdentFromText "cod"
  let lamArgs = (m, z, (m, WeakTermTau)) : map (toPiTypeWith z) bts
  let baseType = (m, WeakTermPi lamArgs (m, WeakTermVar VarKindLocal z))
  case xts of
    [] -> do
      a' <- discernTopLevelName False m $ asIdent a
      let formRule = WeakStmtDef m a' (m, WeakTermTau) (m, WeakTermPi [] (m, WeakTermTau)) -- fake type
      introRuleList <- mapM (stmtDefineDataConstructor m lamArgs baseType a xts) bts
      return $ formRule : introRuleList
    _ -> do
      formRule <- defineFunction False m mFun a xts (m, WeakTermTau) baseType
      introRuleList <- mapM (stmtDefineDataConstructor m lamArgs baseType a xts) bts
      return $ formRule : introRuleList

stmtDefineDataConstructor :: Hint -> [WeakIdentPlus] -> WeakTermPlus -> T.Text -> [WeakIdentPlus] -> (Hint, T.Text, [WeakIdentPlus]) -> IO WeakStmt
stmtDefineDataConstructor m lamArgs baseType a xts (mb, b, yts) = do
  let consArgs = xts ++ yts
  let args = map identPlusToVar yts
  let b' = a <> nsSep <> b
  let indType =
        case xts of
          [] ->
            weakVar m a
          _ ->
            (m, WeakTermPiElim (weakVar m a) (map identPlusToVar xts))
  case consArgs of
    [] ->
      defineTerm
        True
        m
        b'
        indType
        ( m,
          WeakTermPiElim
            (weakVar m "unsafe.cast")
            [ baseType,
              indType,
              ( m,
                WeakTermPiIntro
                  OpacityTransparent
                  (LamKindCons a b')
                  lamArgs
                  (m, WeakTermPiElim (weakVar m b) args)
              )
            ]
        )
    _ ->
      defineFunction
        True
        m
        mb
        b'
        consArgs
        indType
        ( m,
          WeakTermPiElim
            (weakVar m "unsafe.cast")
            [ baseType,
              indType,
              ( m,
                WeakTermPiIntro
                  OpacityTransparent
                  (LamKindCons a b')
                  lamArgs
                  (m, WeakTermPiElim (weakVar m b) args)
              )
            ]
        )

stmtDefineDataClause :: IO (Hint, T.Text, [WeakIdentPlus])
stmtDefineDataClause = do
  token "-"
  m <- currentHint
  b <- symbol
  yts <- many stmtDefineDataClauseArg
  return (m, b, yts)

stmtDefineDataClauseArg :: IO WeakIdentPlus
stmtDefineDataClauseArg = do
  m <- currentHint
  tryPlanList
    [ weakAscription,
      weakTermToWeakIdent m weakTermSimple
    ]

stmtDefineCodata :: IO [WeakStmt]
stmtDefineCodata = do
  m <- currentHint
  token "define-codata"
  mFun <- currentHint
  a <- varText >>= withSectionPrefix
  xts <- many weakAscription
  yts <- many (token "-" >> ascriptionInner)
  formRule <- defineData m mFun a xts [(m, "new", yts)]
  elimRuleList <- mapM (stmtDefineCodataElim m a xts yts) yts
  return $ formRule ++ elimRuleList

stmtDefineCodataElim :: Hint -> T.Text -> [WeakIdentPlus] -> [WeakIdentPlus] -> WeakIdentPlus -> IO WeakStmt
stmtDefineCodataElim m a xts yts (mY, y, elemType) = do
  let codataType =
        case xts of
          [] ->
            weakVar m a
          _ ->
            (m, WeakTermPiElim (weakVar m a) (map identPlusToVar xts))
  recordVarText <- newText
  let projArgs = xts ++ [(m, asIdent recordVarText, codataType)]
  defineFunction
    True
    m
    mY
    (a <> nsSep <> asText y)
    projArgs
    elemType
    ( m,
      WeakTermCase
        elemType
        Nothing
        (weakVar m recordVarText, codataType)
        [((m, asIdent (a <> nsSep <> "new"), yts), weakVar m (asText y))]
    )

stmtDefineResourceType :: IO WeakStmt
stmtDefineResourceType = do
  m <- currentHint
  _ <- token "define-resource-type"
  name <- varText >>= withSectionPrefix
  discarder <- weakTermSimple
  copier <- weakTermSimple
  flag <- newTextualIdentFromText "flag"
  value <- newTextualIdentFromText "value"
  defineTerm
    True
    m
    name
    (m, WeakTermTau)
    ( m,
      WeakTermPiElim
        (weakVar m "unsafe.cast")
        [ ( m,
            WeakTermPi
              [ (m, flag, weakVar m "bool"),
                (m, value, weakVar m "unsafe.pointer")
              ]
              (weakVar m "unsafe.pointer")
          ),
          (m, WeakTermTau),
          ( m,
            WeakTermPiIntro
              OpacityTransparent
              LamKindResourceHandler
              [ (m, flag, (weakVar m "bool")),
                (m, value, (weakVar m "unsafe.pointer"))
              ]
              ( m,
                WeakTermEnumElim
                  ((weakVar m (asText flag)), (weakVar m "bool"))
                  [ ( (m, WeakEnumCaseLabel Nothing "bool.true"),
                      (m, WeakTermPiElim copier [weakVar m (asText value)])
                    ),
                    ( (m, WeakEnumCaseLabel Nothing "bool.false"),
                      ( m,
                        WeakTermPiElim
                          (weakVar m "unsafe.cast")
                          [ (weakVar m "top"),
                            (weakVar m "unsafe.pointer"),
                            (m, WeakTermPiElim discarder [weakVar m (asText value)])
                          ]
                      )
                    )
                  ]
              )
          )
        ]
    )

setAsData :: T.Text -> Int -> [(Hint, T.Text, [WeakIdentPlus])] -> IO ()
setAsData a i bts = do
  let bs = map (\(_, b, _) -> a <> nsSep <> b) bts
  modifyIORef' dataEnv $ \env -> Map.insert a bs env
  forM_ (zip bs [0 ..]) $ \(x, k) ->
    modifyIORef' constructorEnv $ \env -> Map.insert x (i, k) env

toPiTypeWith :: Ident -> (Hint, T.Text, [WeakIdentPlus]) -> WeakIdentPlus
toPiTypeWith cod (m, b, yts) =
  (m, asIdent b, (m, WeakTermPi yts (m, WeakTermVar VarKindLocal cod)))

identPlusToVar :: WeakIdentPlus -> WeakTermPlus
identPlusToVar (m, x, _) =
  (m, WeakTermVar VarKindLocal x)

{-# INLINE isLinear #-}
isLinear :: [Int] -> Bool
isLinear =
  isLinear' S.empty

isLinear' :: S.Set Int -> [Int] -> Bool
isLinear' found input =
  case input of
    [] ->
      True
    (x : xs)
      | x `S.member` found ->
        False
      | otherwise ->
        isLinear' (S.insert x found) xs

insEnumEnv :: Hint -> T.Text -> [(T.Text, Int)] -> IO ()
insEnumEnv m name xis = do
  path <- getCurrentFilePath
  eenv <- readIORef enumEnv
  let definedEnums = Map.keys eenv ++ map fst (concat $ map snd (Map.elems eenv))
  case find (`elem` definedEnums) $ name : map fst xis of
    Just x ->
      raiseError m $ "the constant `" <> x <> "` is already defined [ENUM]"
    _ -> do
      let (xs, is) = unzip xis
      let rev = Map.fromList $ zip xs (zip3 (repeat path) (repeat name) is)
      modifyIORef' enumEnv $ \env -> Map.insert name (path, xis) env
      modifyIORef' revEnumEnv $ \env -> Map.union rev env

varText :: IO T.Text
varText =
  snd <$> var
