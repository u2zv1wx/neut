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

parse :: Path Abs File -> IO [WeakStmt]
parse path = do
  pushTrace path
  visit path

visit :: Path Abs File -> IO [WeakStmt]
visit path = do
  pushTrace path
  modifyIORef' fileEnv $ \env -> Map.insert path VisitInfoActive env
  withNestedState $ do
    TIO.readFile (toFilePath path) >>= initializeState
    skip
    stmt

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

stmt :: IO [WeakStmt]
stmt = do
  s <- readIORef text
  if T.null s
    then leave
    else do
      headSymbol <- lookAhead symbolMaybe
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
        Just "reduce" -> do
          def <- stmtReduce
          stmtList <- stmt
          return $ def : stmtList
        Just "include" ->
          stmtInclude
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
        Just "ensure" -> do
          stmtEnsure
          stmt
        Just "section" ->
          stmtSection
        Just "end" ->
          stmtEnd
        Just "define-prefix" -> do
          stmtDefinePrefix
          stmt
        Just "remove-prefix" -> do
          stmtRemovePrefix
          stmt
        Just "use" -> do
          stmtUse
          stmt
        Just "unuse" -> do
          stmtUnuse
          stmt
        _ -> do
          def <- stmtAux
          defList <- stmt
          return $ def : defList

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
  -- token "define" -- fixme: define-opaque
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
  (_, funName'', piType') <- discernIdentPlus (m, asIdent funName', piType)
  e' <- discern (m, WeakTermPiIntro OpacityTranslucent (LamKindFix (mFun, asIdent funName', piType)) argList e)
  return $ WeakStmtDef m (Just (isReducible, funName'')) piType' e'

defineTerm :: IsReducible -> Hint -> T.Text -> WeakTermPlus -> WeakTermPlus -> IO WeakStmt
defineTerm isReducible m funName' codType e = do
  (_, funName'', codType') <- discernIdentPlus (m, asIdent funName', codType)
  e' <- discern e
  return $ WeakStmtDef m (Just (isReducible, funName'')) codType' e'

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

stmtReduce :: IO WeakStmt
stmtReduce = do
  m <- currentHint
  token "reduce"
  e <- weakTerm >>= discern
  t <- newAster m
  return $ WeakStmtDef m Nothing t e

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
    -- urlStr' <- readStrOrThrow mUrl urlStr
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

-- readStrOrThrow :: Hint -> T.Text -> IO String
-- readStrOrThrow m quotedStr =
--   case readMaybe (T.unpack $ "\"" <> quotedStr) of
--     Nothing -> do
--       p' quotedStr
--       p' (T.unpack quotedStr)
--       raiseError m "the atom here must be a string"
--     Just str ->
--       return str

raiseIfFailure :: Hint -> String -> ExitCode -> Handle -> Path Abs Dir -> IO ()
raiseIfFailure m procName exitCode h pkgDirPath =
  case exitCode of
    ExitSuccess ->
      return ()
    ExitFailure i -> do
      removeDir pkgDirPath
      errStr <- hGetContents h
      raiseError m $ T.pack $ "the child process `" ++ procName ++ "` failed with the following message (exitcode = " ++ show i ++ "):\n" ++ errStr

stmtSection :: IO [WeakStmt]
stmtSection = do
  token "section"
  item <- varText
  handleSection item stmt

stmtEnd :: IO [WeakStmt]
stmtEnd = do
  m <- currentHint
  token "end"
  item <- varText
  handleEnd m item stmt

stmtUse :: IO ()
stmtUse = do
  token "use"
  name <- varText
  use name

stmtUnuse :: IO ()
stmtUnuse = do
  token "unuse"
  name <- varText
  unuse name

stmtAux :: IO WeakStmt
stmtAux = do
  m <- currentHint
  e <- weakTerm >>= discern
  t <- newAster m
  return $ WeakStmtDef m Nothing t e

stmtDefinePrefix :: IO ()
stmtDefinePrefix = do
  token "define-prefix"
  from <- varText
  token "="
  to <- varText
  modifyIORef' nsEnv $ \env -> (from, to) : env

stmtRemovePrefix :: IO ()
stmtRemovePrefix = do
  token "remove-prefix"
  from <- varText
  token "="
  to <- varText
  modifyIORef' nsEnv $ \env -> filter (/= (from, to)) env

stmtInclude :: IO [WeakStmt]
stmtInclude = do
  m <- currentHint
  ensureEnvSanity m
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
      stmt
    Nothing -> do
      defList1 <- visit newPath
      defList2 <- stmt
      return $ defList1 ++ defList2

ensureEnvSanity :: Hint -> IO ()
ensureEnvSanity m = do
  penv <- readIORef prefixEnv
  if null penv
    then return ()
    else raiseError m $ "`include` can only be used with no `use`, but the current `use` is: " <> T.intercalate ", " penv

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
  z <- newIdentFromText "cod"
  let lamArgs = (m, z, (m, WeakTermTau)) : map (toPiTypeWith z) bts
  let baseType = (m, WeakTermPi lamArgs (m, WeakTermVar VarKindLocal z))
  case xts of
    [] -> do
      (_, a', tau) <- discernIdentPlus (m, asIdent a, (m, WeakTermTau))
      let formRule = WeakStmtDef m (Just (False, a')) tau (m, WeakTermPi [] (m, WeakTermTau)) -- fake type
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
      weakTermToWeakIdent m (betweenParen weakTerm),
      weakTermToWeakIdent m weakTermTau,
      weakTermToWeakIdent m weakTermVar
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
  flag <- newIdentFromText "flag"
  value <- newIdentFromText "value"
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
                  [ ( (m, EnumCaseLabel "bool.true"),
                      (m, WeakTermPiElim copier [weakVar m (asText value)])
                    ),
                    ( (m, EnumCaseLabel "bool.false"),
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

-- defineFunction
--   True
--   m
--   mFun
--   name
--   []
--   (m, WeakTermTau)
--   ( m,
--     WeakTermPiElim
--       (weakVar m "unsafe.cast")
--       [ ( m,
--           WeakTermPi
--             [ (m, flag, weakVar m "bool"),
--               (m, value, weakVar m "unsafe.pointer")
--             ]
--             (weakVar m "unsafe.pointer")
--         ),
--         (m, WeakTermTau),
--         ( m,
--           WeakTermPiIntro
--             OpacityTransparent
--             LamKindResourceHandler
--             [ (m, flag, (weakVar m "bool")),
--               (m, value, (weakVar m "unsafe.pointer"))
--             ]
--             ( m,
--               WeakTermEnumElim
--                 ((weakVar m (asText flag)), (weakVar m "bool"))
--                 [ ( (m, EnumCaseLabel "bool.true"),
--                     (m, WeakTermPiElim copier [weakVar m (asText value)])
--                   ),
--                   ( (m, EnumCaseLabel "bool.false"),
--                     ( m,
--                       WeakTermPiElim
--                         (weakVar m "unsafe.cast")
--                         [ (weakVar m "top"),
--                           (weakVar m "unsafe.pointer"),
--                           (m, WeakTermPiElim discarder [weakVar m (asText value)])
--                         ]
--                     )
--                   )
--                 ]
--             )
--         )
--       ]
--   )

weakTermToWeakIdent :: Hint -> IO WeakTermPlus -> IO WeakIdentPlus
weakTermToWeakIdent m f = do
  a <- f
  txt <- newText
  h <- newIdentFromText txt
  return (m, h, a)

setAsData :: T.Text -> Int -> [(Hint, T.Text, [WeakIdentPlus])] -> IO ()
setAsData a i bts = do
  -- let proj (_, y, _) = y
  let bs = map (\(_, b, _) -> a <> nsSep <> b) bts
  -- bs <- mapM (withSectionPrefix . proj) bts
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
  eenv <- readIORef enumEnv
  let definedEnums = Map.keys eenv ++ map fst (concat (Map.elems eenv))
  case find (`elem` definedEnums) $ name : map fst xis of
    Just x ->
      raiseError m $ "the constant `" <> x <> "` is already defined [ENUM]"
    _ -> do
      let (xs, is) = unzip xis
      let rev = Map.fromList $ zip xs (zip (repeat name) is)
      modifyIORef' enumEnv $ \env -> Map.insert name xis env
      modifyIORef' revEnumEnv $ \env -> Map.union rev env
