module Preprocess.Parse
  ( visitP,
  )
where

import Codec.Binary.UTF8.String
import Control.Exception.Safe
import Control.Monad (forM, when)
import Data.Basic
import Data.Global
import qualified Data.HashMap.Lazy as Map
import Data.IORef
import Data.List (find)
import Data.Log
import Data.LowType
import Data.Namespace
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.WeakTerm
import GHC.IO.Handle
import Parse.Discern
import Path
import Path.IO
import System.Exit
import System.IO.Unsafe (unsafePerformIO)
import System.Process hiding (env)
import Text.Read (readMaybe)

type EscapeFlag =
  Bool

--
-- states
--

-- raiseParseErrorはhintを受け取るようにするべきかも。

{-# NOINLINE text #-}
text :: IORef T.Text
text =
  unsafePerformIO (newIORef "")

{-# NOINLINE line #-}
line :: IORef Int
line =
  unsafePerformIO (newIORef 1)

{-# NOINLINE column #-}
column :: IORef Int
column =
  unsafePerformIO (newIORef 1)

-- parseStmt :: T.Text -> IO [WeakStmt]
-- parseStmt input = do
--   modifyIORef' text $ \_ -> input
--   skip
--   stmt

-- parseWeakTerm :: T.Text -> IO WeakTermPlus
-- parseWeakTerm input = do
--   modifyIORef' text $ \_ -> input
--   skip
--   weakTerm

visitP :: Path Abs File -> IO [WeakStmt]
visitP path = do
  pushTrace path
  modifyIORef' fileEnv $ \env -> Map.insert path VisitInfoActive env
  withNestedState $ do
    TIO.readFile (toFilePath path) >>= initializeState
    skip
    stmt

-- initializeStateみたいなのがいる？

-- return

-- state <- saveState
-- modifyIORef' text $ \_ -> content
-- skip
-- defList <- stmt
-- loadState state
-- return defList

-- tokenize content >>= preprocess'

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
          def <- stmtDefine
          stmtList <- stmt
          return $ def : stmtList
        Just "define-enum" -> do
          stmtDefineEnum
          stmt
        Just "include" ->
          stmtInclude
        Just "define-data" ->
          undefined
        Just "define-codata" ->
          undefined
        Just "introspect" ->
          undefined
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
stmtDefine :: IO WeakStmt
stmtDefine = do
  m <- currentHint
  token "define"
  (mFun, funName) <- var
  funName' <- withSectionPrefix funName
  argList <- many weakIdentPlus
  token ":"
  codType <- weakTerm
  token "="
  e <- weakTerm
  case argList of
    [] -> do
      e' <- discern e
      (_, funName'', codType') <- discernIdentPlus (mFun, asIdent funName', codType)
      return $ WeakStmtDef m (Just (True, funName'')) codType' e'
    _ -> do
      let piType = (m, WeakTermPi argList codType)
      (_, funName'', piType') <- discernIdentPlus (m, asIdent funName', piType)
      e' <- discern (m, WeakTermPiIntro OpacityTransparent (LamKindFix (mFun, asIdent funName', piType)) argList e)
      return $ WeakStmtDef m (Just (True, funName'')) piType' e'

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
    urlStr' <- readStrOrThrow mUrl urlStr
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

readStrOrThrow :: (Read a) => Hint -> T.Text -> IO a
readStrOrThrow m quotedStr =
  case readMaybe (T.unpack quotedStr) of
    Nothing ->
      raiseError m "the atom here must be a string"
    Just str ->
      return str

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

-- let piType = (m, WeakTermPi argList codType)
-- let e' = (m, WeakTermPiIntro OpacityTransparent (LamKindFix (m, asIdent funName, piType)) argList e)
-- return $ WeakStmtDef m (Just (True, asIdent funName)) piType e'

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
      defList1 <- visitP newPath
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

--
-- parser for WeakTerm
--

weakTerm :: IO WeakTermPlus
weakTerm = do
  headSymbol <- lookAhead symbolMaybe
  case headSymbol of
    Just "pi" ->
      weakTermPi
    Just "lambda" ->
      weakTermPiIntro
    Just "fix" ->
      weakTermPiIntroFix
    Just "*" ->
      weakTermAster
    Just "switch" ->
      weakTermEnumElim
    Just "question" ->
      weakTermQuestion
    Just "derangement" ->
      weakTermDerangement
    Just "match" ->
      weakTermMatch
    Just "match-noetic" ->
      weakTermMatchNoetic
    Just "let" ->
      weakTermLet
    Just "let?" ->
      weakTermLetCoproduct
    Just "if" ->
      weakTermIf
    Just "sigma" ->
      weakTermSigma
    Just "product" ->
      weakTermProduct
    Just "idealize" ->
      weakTermIdealize
    _ ->
      weakTermAux

weakTermTau :: IO WeakTermPlus
weakTermTau = do
  m <- currentHint
  token "tau"
  return (m, WeakTermTau)

weakTermAster :: IO WeakTermPlus
weakTermAster = do
  m <- currentHint
  token "*"
  h <- newAster m
  return h

weakTermPi :: IO WeakTermPlus
weakTermPi = do
  m <- currentHint
  token "pi"
  varList <- many weakIdentPlus
  char '.' >> skip
  e <- weakTerm
  return (m, WeakTermPi varList e)

weakTermPiIntro :: IO WeakTermPlus
weakTermPiIntro = do
  m <- currentHint
  token "lambda"
  varList <- many weakIdentPlus
  char '.' >> skip
  e <- weakTerm
  return (m, WeakTermPiIntro OpacityTransparent LamKindNormal varList e)

weakTermPiIntroFix :: IO WeakTermPlus
weakTermPiIntroFix = do
  m <- currentHint
  token "fix"
  self <- weakIdentPlus
  varList <- many weakIdentPlus
  char '.' >> skip
  e <- weakTerm
  return (m, WeakTermPiIntro OpacityTransparent (LamKindFix self) varList e)

weakTermAux :: IO WeakTermPlus
weakTermAux = do
  m <- currentHint
  e <- weakTermSimple
  es <- many weakTermSimple
  if null es
    then return e
    else return (m, WeakTermPiElim e es)

weakTermEnumElim :: IO WeakTermPlus
weakTermEnumElim = do
  m <- currentHint
  token "switch"
  e <- weakTerm
  token "with"
  clauseList <- many weakTermEnumClause
  token "end"
  h <- newAster m
  return (m, WeakTermEnumElim (e, h) clauseList)

weakTermEnumClause :: IO (EnumCasePlus, WeakTermPlus)
weakTermEnumClause = do
  headSymbol <- lookAhead symbol
  if headSymbol == "end"
    then raiseParseError "end"
    else do
      m <- currentHint
      token "-"
      c <- symbol
      token "->"
      body <- weakTerm
      case c of
        "default" ->
          return ((m, EnumCaseDefault), body)
        _ ->
          return ((m, EnumCaseLabel c), body)

-- question e
weakTermQuestion :: IO WeakTermPlus
weakTermQuestion = do
  m <- currentHint
  token "question"
  e <- weakTerm
  h <- newAster m
  return (m, WeakTermQuestion e h)

-- derangement KIND with
-- - arg-1
-- - ...
-- - arg-n
-- end
weakTermDerangement :: IO WeakTermPlus
weakTermDerangement = do
  m <- currentHint
  token "derangement"
  k <- weakTermDerangementKind
  token "with"
  es <- many (token "-" >> weakTerm)
  token "end"
  return (m, WeakTermDerangement k es)

weakTermDerangementKind :: IO Derangement
weakTermDerangementKind = do
  s <- saveState
  headSymbol <- symbol
  case headSymbol of
    "nop" ->
      return DerangementNop
    "store" -> do
      t <- lowTypeSimple
      return $ DerangementStore t
    "load" -> do
      t <- lowTypeSimple
      return $ DerangementLoad t
    "create-array" -> do
      t <- lowTypeSimple
      return $ DerangementCreateArray t
    "create-struct" -> do
      ts <- many lowTypeSimple
      return $ DerangementCreateStruct ts
    "syscall" -> do
      syscallNum <- integer
      return $ DerangementSyscall syscallNum
    "external" -> do
      f <- symbol
      return $ DerangementExternal f
    _ -> do
      loadState s
      raiseParseError "derangement"

-- t ::= i{n} | f{n} | pointer t | array INT t | struct t ... t
lowType :: IO LowType
lowType = do
  s <- saveState
  headSymbol <- symbol
  case headSymbol of
    "pointer" -> do
      t <- lowTypeSimple
      return $ LowTypePointer t
    "array" -> do
      intValue <- integer
      t <- lowTypeSimple
      return $ LowTypeArray (fromInteger intValue) t
    "struct" -> do
      ts <- many lowTypeSimple
      return $ LowTypeStruct ts
    _
      | Just size <- asLowInt headSymbol ->
        return $ LowTypeInt size
      | Just size <- asLowFloat headSymbol ->
        return $ LowTypeFloat size
      | otherwise -> do
        loadState s
        raiseParseError "lowType"

lowTypeSimple :: IO LowType
lowTypeSimple = do
  tryPlanList
    [ betweenParen lowType,
      lowTypeInt,
      lowTypeFloat,
      raiseParseError "lowTypeSimple"
    ]

lowTypeInt :: IO LowType
lowTypeInt = do
  headSymbol <- symbol
  case asLowInt headSymbol of
    Just size ->
      return $ LowTypeInt size
    Nothing ->
      raiseParseError "lowTypeInt"

lowTypeFloat :: IO LowType
lowTypeFloat = do
  headSymbol <- symbol
  case asLowFloat headSymbol of
    Just size ->
      return $ LowTypeFloat size
    Nothing ->
      raiseParseError "lowTypeFloat"

weakTermMatch :: IO WeakTermPlus
weakTermMatch = do
  m <- currentHint
  token "match"
  e <- weakTerm
  token "with"
  clauseList <- many weakTermMatchClause
  token "end"
  return (m, WeakTermCase (doNotCare m) Nothing (e, doNotCare m) clauseList)

weakTermMatchNoetic :: IO WeakTermPlus
weakTermMatchNoetic = do
  m <- currentHint
  token "match-noetic"
  e <- weakTerm
  token "with"
  s <- newAster m
  t <- newAster m
  let e' = castFromNoema s t e
  clauseList <- many weakTermMatchClause
  token "end"
  let clauseList' = map (modifyWeakPattern s) clauseList
  return (m, WeakTermCase (doNotCare m) (Just s) (e', doNotCare m) clauseList')

weakTermMatchClause :: IO (WeakPattern, WeakTermPlus)
weakTermMatchClause = do
  headSymbol <- lookAhead symbol
  if headSymbol == "end"
    then raiseParseError "end"
    else do
      token "-"
      pat <- weakTermPattern
      body <- weakTerm
      return (pat, body)

modifyWeakPattern :: WeakTermPlus -> (WeakPattern, WeakTermPlus) -> (WeakPattern, WeakTermPlus)
modifyWeakPattern s ((m, a, xts), body) =
  ((m, a, xts), modifyWeakPatternBody s xts body)

modifyWeakPatternBody :: WeakTermPlus -> [WeakIdentPlus] -> WeakTermPlus -> WeakTermPlus
modifyWeakPatternBody s xts body =
  case xts of
    [] ->
      body
    ((m, x, t) : rest) -> do
      ( m,
        WeakTermPiElim
          ( m,
            WeakTermPiIntro
              OpacityTransparent
              LamKindNormal
              [(m, x, wrapWithNoema s t)]
              (modifyWeakPatternBody s rest body)
          )
          [castToNoema s t (m, WeakTermVar VarKindLocal x)]
        )

weakTermPattern :: IO WeakPattern
weakTermPattern = do
  m <- currentHint
  c <- simpleSymbol
  argList <- weakTermPatternArgument
  return (m, asIdent c, argList)

weakTermPatternArgument :: IO [WeakIdentPlus]
weakTermPatternArgument = do
  m <- currentHint
  x <- symbol
  skip
  if x == "->"
    then return []
    else do
      tmp <- weakTermPatternArgument
      h <- newAster m
      return $ (m, asIdent x, h) : tmp

-- let x : A = e1 in e2
-- let x     = e1 in e2
weakTermLet :: IO WeakTermPlus
weakTermLet =
  tryPlanList [weakTermLetSigmaElim, weakTermLetNormal]

weakTermLetNormal :: IO WeakTermPlus
weakTermLetNormal = do
  m <- currentHint
  token "let"
  x <- weakTermLetVar
  char '=' >> skip
  e1 <- weakTerm
  token "in"
  e2 <- weakTerm
  return (m, WeakTermPiElim (m, WeakTermPiIntro OpacityTransparent LamKindNormal [x] e2) [e1])

weakTermSigmaElimVar :: IO WeakIdentPlus
weakTermSigmaElimVar =
  tryPlanList [ascriptionInner, weakAscription']

-- let (x1 : A1, ..., xn : An) = e1 in e2
weakTermLetSigmaElim :: IO WeakTermPlus
weakTermLetSigmaElim = do
  m <- currentHint
  token "let"
  xts <- betweenParen $ sepBy2 weakTermSigmaElimVar (char ',' >> skip)
  token "="
  e1 <- weakTerm
  token "in"
  e2 <- weakTerm
  resultType <- newAster m
  return
    ( m,
      WeakTermPiElim
        e1
        [ resultType,
          (m, WeakTermPiIntro OpacityTransparent LamKindNormal xts e2)
        ]
    )

-- let? x : A = e1 in e2
-- let? x     = e1 in e2
weakTermLetCoproduct :: IO WeakTermPlus
weakTermLetCoproduct = do
  m <- currentHint
  token "let?"
  x <- weakTermLetVar
  char '=' >> skip
  e1 <- weakTerm
  token "in"
  e2 <- weakTerm
  err <- newIdentFromText "err"
  typeOfLeft <- newAster m
  typeOfRight <- newAster m
  let coproductLeft = asIdent "coproduct.left"
  return
    ( m,
      WeakTermCase
        (doNotCare m)
        Nothing
        (e1, doNotCare m)
        [ ( (m, coproductLeft, [(m, err, typeOfLeft)]),
            (m, WeakTermPiElim (m, WeakTermVar VarKindLocal coproductLeft) [typeOfLeft, typeOfRight, (m, WeakTermVar VarKindLocal err)])
          ),
          ( (m, asIdent "coproduct.right", [x]),
            e2
          )
        ]
    )

weakTermLetVar :: IO WeakIdentPlus
weakTermLetVar = do
  m <- currentHint
  tryPlanList
    [ do
        x <- simpleSymbol
        char ':'
        skip
        a <- weakTerm
        return (m, asIdent x, a),
      do
        x <- simpleSymbol
        h <- newAster m
        return (m, asIdent x, h)
    ]

weakTermIf :: IO WeakTermPlus
weakTermIf = do
  m <- currentHint
  token "if"
  e1 <- weakTerm
  token "then"
  e2 <- weakTerm
  token "else"
  e3 <- weakTerm
  token "end"
  h <- newAster m
  return
    ( m,
      WeakTermEnumElim
        (e1, h)
        [ ((m, EnumCaseLabel "bool.true"), e2),
          ((m, EnumCaseLabel "bool.false"), e3)
        ]
    )

-- sigma (x1 : A1) ... (xn : An). B
weakTermSigma :: IO WeakTermPlus
weakTermSigma = do
  m <- currentHint
  token "sigma"
  varList <- many weakIdentPlus
  char '.' >> skip
  cod <- weakTerm
  h <- newIdentFromText "_"
  toSigma m $ varList ++ [(m, h, cod)]

-- product e1 ... en
weakTermProduct :: IO WeakTermPlus
weakTermProduct = do
  m <- currentHint
  token "product"
  ts <- many weakTermSimple
  xs <- mapM (const $ newIdentFromText "_") ts
  toSigma m $ zipWith (\x t -> (m, x, t)) xs ts

-- (e1, ..., en) (n >= 2)
weakTermSigmaIntro :: IO WeakTermPlus
weakTermSigmaIntro = do
  m <- currentHint
  betweenParen $ do
    es <- sepBy2 weakTerm (char ',' >> skip)
    xts <- forM es $ \_ -> do
      x <- newIdentFromText "_"
      t <- newAster m
      return (m, x, t)
    sigVar <- newIdentFromText "sigvar"
    k <- newIdentFromText "sig-k"
    return
      ( m,
        WeakTermPiIntro
          OpacityTransparent
          LamKindNormal
          [ (m, sigVar, (m, WeakTermTau)),
            (m, k, (m, WeakTermPi xts (m, WeakTermVar VarKindLocal sigVar)))
          ]
          (m, WeakTermPiElim (m, WeakTermVar VarKindLocal k) es)
      )

weakTermIdealize :: IO WeakTermPlus
weakTermIdealize = do
  m <- currentHint
  token "idealize"
  varList <- many var
  let varList' = fmap (fmap asIdent) varList
  token "over"
  mSubject <- currentHint
  subject <- simpleSymbol
  token "in"
  e <- weakTerm
  resultType <- newAster m
  let subjectTerm = (mSubject, WeakTermVar VarKindLocal (asIdent subject))
  ts <- mapM (\(mx, _) -> newAster mx) varList
  return
    ( m,
      WeakTermPiElim
        (m, WeakTermVar VarKindLocal (asIdent "idea.run"))
        [ resultType,
          ( m,
            WeakTermPiIntro
              OpacityTransparent
              LamKindNormal
              [(mSubject, asIdent subject, (m, WeakTermVar VarKindLocal (asIdent "subject")))]
              (castLet subjectTerm (zip varList' ts) e)
          )
        ]
    )

castLet :: WeakTermPlus -> [((Hint, Ident), WeakTermPlus)] -> WeakTermPlus -> WeakTermPlus
castLet subject xts cont =
  case xts of
    [] ->
      cont
    ((m, x), t) : rest ->
      ( m,
        WeakTermPiElim
          ( m,
            WeakTermPiIntro
              OpacityTransparent
              LamKindNormal
              [(m, x, wrapWithNoema subject t)] -- shadowing
              (castLet subject rest cont)
          )
          [castToNoema subject t (m, WeakTermVar VarKindLocal x)] -- FIXME: ここでxをdo-not-consumeに包むべき
      )

--
-- term-related helper functions
--

weakTermSimple :: IO WeakTermPlus
weakTermSimple = do
  tryPlanList
    [ weakTermSigmaIntro,
      betweenParen weakTerm,
      weakTermTau,
      weakTermString,
      weakTermInteger,
      weakTermFloat,
      weakTermVar
    ]

weakIdentPlus :: IO WeakIdentPlus
weakIdentPlus = do
  tryPlanList
    [ weakAscription,
      weakAscription'
    ]

ascriptionInner :: IO WeakIdentPlus
ascriptionInner = do
  m <- currentHint
  x <- symbol
  char ':' >> skip
  a <- weakTerm
  return (m, asIdent x, a)

weakAscription :: IO WeakIdentPlus
weakAscription = do
  betweenParen ascriptionInner

weakAscription' :: IO WeakIdentPlus
weakAscription' = do
  (m, x) <- weakSimpleIdent
  h <- newAster m
  return (m, x, h)

weakSimpleIdent :: IO (Hint, Ident)
weakSimpleIdent = do
  m <- currentHint
  x <- simpleSymbol
  if isKeyword x
    then raiseParseError $ "found a keyword `" <> x <> "`, expecting a variable"
    else return (m, asIdent x)

var :: IO (Hint, T.Text)
var = do
  m <- currentHint
  x <- symbol
  if isKeyword x
    then raiseParseError $ "found a reserved symbol `" <> x <> "`, expecting a variable"
    else return (m, x)

varText :: IO T.Text
varText =
  snd <$> var

weakTermVar :: IO WeakTermPlus
weakTermVar = do
  (m, x) <- var
  return (m, WeakTermVar VarKindLocal $ asIdent x)

weakTermString :: IO WeakTermPlus
weakTermString = do
  m <- currentHint
  s <- string
  let i8s = encode $ T.unpack s
  let len = toInteger $ length i8s
  let i8s' = map (\x -> (m, WeakTermInt (m, WeakTermConst "i8") (toInteger x))) i8s
  return
    ( m,
      WeakTermPiElim
        (m, WeakTermVar VarKindLocal (asIdent "unsafe.create-new-string"))
        [ (m, WeakTermInt (m, WeakTermConst "i64") len),
          ( m,
            WeakTermDerangement
              (DerangementCreateArray (LowTypeInt 32))
              i8s'
          )
        ]
    )

weakTermInteger :: IO WeakTermPlus
weakTermInteger = do
  m <- currentHint
  intValue <- integer
  h <- newAster m
  return (m, WeakTermInt h intValue)

integer :: IO Integer
integer = do
  x <- symbol
  case readMaybe (T.unpack x) of
    Just intValue ->
      return intValue
    Nothing ->
      raiseParseError $ "unexpected symbol: " <> x <> "\n expecting: an integer"

weakTermFloat :: IO WeakTermPlus
weakTermFloat = do
  m <- currentHint
  x <- symbol
  case readMaybe (T.unpack x) of
    Just floatValue -> do
      h <- newAster m
      return (m, WeakTermFloat h floatValue)
    Nothing ->
      raiseParseError $ "unexpected symbol: " <> x <> "\n expecting: an integer"

toSigma :: Hint -> [WeakIdentPlus] -> IO WeakTermPlus
toSigma m xts = do
  sigVar <- newIdentFromText "sig"
  h <- newIdentFromText "_"
  return
    ( m,
      WeakTermPi
        [ (m, sigVar, (m, WeakTermTau)),
          (m, h, (m, WeakTermPi xts (m, WeakTermVar VarKindLocal sigVar)))
        ]
        (m, WeakTermVar VarKindLocal sigVar)
    )

castFromNoema :: WeakTermPlus -> WeakTermPlus -> WeakTermPlus -> WeakTermPlus
castFromNoema subject baseType tree = do
  let m = fst tree
  ( m,
    WeakTermPiElim
      (m, WeakTermVar VarKindLocal (asIdent "unsafe.cast"))
      [ wrapWithNoema subject baseType,
        baseType,
        tree
      ]
    )

castToNoema :: WeakTermPlus -> WeakTermPlus -> WeakTermPlus -> WeakTermPlus
castToNoema subject baseType tree = do
  let m = fst tree
  ( m,
    WeakTermPiElim
      (m, WeakTermVar VarKindLocal (asIdent "unsafe.cast"))
      [ baseType,
        wrapWithNoema subject baseType,
        tree
      ]
    )

wrapWithNoema :: WeakTermPlus -> WeakTermPlus -> WeakTermPlus
wrapWithNoema subject baseType = do
  let m = fst baseType
  (m, WeakTermPiElim (m, WeakTermVar VarKindLocal (asIdent "noema")) [subject, baseType])

doNotCare :: Hint -> WeakTermPlus
doNotCare m =
  (m, WeakTermTau)

--
-- basic functions for the parser combinator
--

type ParserState = (T.Text, Int, Int)

saveState :: IO ParserState
saveState = do
  s <- readIORef text
  l <- readIORef line
  c <- readIORef column
  return (s, l, c)

loadState :: ParserState -> IO ()
loadState (s, l, c) = do
  writeIORef text s
  writeIORef line l
  writeIORef column c

initializeState :: T.Text -> IO ()
initializeState fileContent = do
  writeIORef line 1
  writeIORef column 1
  writeIORef text fileContent

-- modifyIORef' text $ \_ -> content

withNestedState :: IO a -> IO a
withNestedState comp = do
  state <- saveState
  value <- comp
  loadState state
  return value

betweenParen :: IO a -> IO a
betweenParen f = do
  char '(' >> skip
  item <- f
  char ')' >> skip
  return item

token :: T.Text -> IO ()
token expected = do
  actual <- symbol
  if actual == expected
    then return ()
    else raiseParseError $ "found an unexpected token `" <> actual <> "`, expecting: " <> expected

char :: Char -> IO ()
char c = do
  s <- readIORef text
  case T.uncons s of
    Nothing ->
      raiseParseError $
        "unexpected end of input\nexpecting: '" <> T.singleton c <> "'"
    Just (c', rest)
      | c == c' ->
        if c `S.member` newlineSet
          then updateStreamL rest
          else updateStreamC 1 rest
      | otherwise ->
        raiseParseError $
          "unexpected character: '"
            <> T.singleton c'
            <> "'\nexpecting: '"
            <> T.singleton c
            <> "'"

skip :: IO ()
skip = do
  s <- readIORef text
  case T.uncons s of
    Just (c, rest)
      | c == ';' ->
        comment
      | c `S.member` newlineSet ->
        updateStreamL rest >> skip
      | c `S.member` spaceSet ->
        updateStreamC 1 rest >> skip
    _ ->
      return ()

comment :: IO ()
comment = do
  s <- readIORef text
  case T.uncons s of
    Just (c, rest)
      | c `S.member` newlineSet ->
        updateStreamL rest >> skip
      | otherwise ->
        updateStreamC 1 rest >> comment
    Nothing ->
      return ()

many :: IO a -> IO [a]
many f = do
  tryPlanList
    [ do
        x <- f
        xs <- many f
        return $ x : xs,
      return []
    ]

-- s <- saveState
-- item <- catch f (helper s (loadState s >> return []))
-- sepEndBy f (return ())

-- many :: IO a -> IO [a]
-- many f =
--   sepEndBy f (return ())

tryPlanList :: [IO a] -> IO a
tryPlanList planList =
  case planList of
    [] ->
      raiseParseError "empty planList"
    [f] ->
      f
    f : fs -> do
      s <- saveState
      catch f (helper s (tryPlanList fs))

helper :: ParserState -> IO a -> Error -> IO a
helper s g _ = do
  loadState s
  g

lookAhead :: IO a -> IO a
lookAhead f = do
  s <- saveState
  result <- f
  loadState s
  return result

sepBy2 :: IO a -> IO b -> IO [a]
sepBy2 f sep = do
  item1 <- f
  _ <- sep
  item2 <- f
  itemList <- many $ sep >> f
  return $ item1 : item2 : itemList

-- sepEndBy :: IO a -> IO () -> IO [a]
-- sepEndBy f g =
--   sepEndBy' (f >>= return . Right) g []

-- sepEndBy' :: IO (Either [a] a) -> IO () -> [a] -> IO [a]
-- sepEndBy' f g acc = do
--   itemOrResult <- catch f (finalize acc)
--   g
--   case itemOrResult of
--     Right item ->
--       sepEndBy' f g (item : acc)
--     Left result ->
--       return result

-- finalize :: [a] -> Error -> IO (Either [a] a)
-- finalize acc _ =
--   return $ Left $ reverse acc

symbol :: IO T.Text
symbol = do
  s <- readIORef text
  let x = T.takeWhile isSymbolChar s
  let rest = T.dropWhile isSymbolChar s
  updateStreamC (T.length x) rest
  skip
  if T.null x
    then raiseParseError "empty symbol"
    else return x

symbolMaybe :: IO (Maybe T.Text)
symbolMaybe = do
  s <- readIORef text
  let x = T.takeWhile isSymbolChar s
  let rest = T.dropWhile isSymbolChar s
  updateStreamC (T.length x) rest
  skip
  if T.null x
    then return Nothing
    else return $ Just x

simpleSymbol :: IO T.Text
simpleSymbol = do
  s <- readIORef text
  let x = T.takeWhile isSimpleSymbolChar s
  let rest = T.dropWhile isSimpleSymbolChar s
  updateStreamC (T.length x) rest
  skip
  if T.null x
    then raiseParseError "empty symbol"
    else return x

string :: IO T.Text
string = do
  char '"'
  s <- readIORef text
  len <- stringLengthOf False s 0
  let (x, s') = T.splitAt len s
  writeIORef text $ T.tail s'
  skip
  return x

-- headStringLengthOf :: EscapeFlag -> T.Text -> Int -> IO Int
-- headStringLengthOf flag s i =
--   case T.uncons s of
--     Nothing ->
--       raiseParseError "unexpected end of input while parsing string"
--     Just (c, rest)
--       | c == '"' -> do
--         incrementColumn
--         if flag
--           then headStringLengthOf False rest (i + 1)
--           else return $ i + 1
--       | c == '\\' -> do
--         incrementColumn
--         headStringLengthOf (not flag) rest (i + 1)
--       | c `S.member` newlineSet -> do
--         incrementLine
--         headStringLengthOf False rest (i + 1)
--       | otherwise -> do
--         incrementColumn
--         headStringLengthOf False rest (i + 1)

stringLengthOf :: EscapeFlag -> T.Text -> Int -> IO Int
stringLengthOf flag s i =
  case T.uncons s of
    Nothing ->
      raiseParseError "unexpected end of input while parsing string"
    Just (c, rest)
      | c == '"' -> do
        incrementColumn
        if flag
          then stringLengthOf False rest (i + 1)
          else return i
      | c == '\\' -> do
        incrementColumn
        stringLengthOf (not flag) rest (i + 1)
      | c `S.member` newlineSet -> do
        incrementLine
        stringLengthOf False rest (i + 1)
      | otherwise -> do
        incrementColumn
        stringLengthOf False rest (i + 1)

currentHint :: IO Hint
currentHint = do
  l <- readIORef line
  c <- readIORef column
  path <- getCurrentFilePath
  return $ newHint (fromEnum l) (fromEnum c) path

{-# INLINE isSymbolChar #-}
isSymbolChar :: Char -> Bool
isSymbolChar c =
  c `S.notMember` nonSymbolSet

{-# INLINE isSimpleSymbolChar #-}
isSimpleSymbolChar :: Char -> Bool
isSimpleSymbolChar c =
  c `S.notMember` nonSimpleSymbolSet

{-# INLINE spaceSet #-}
spaceSet :: S.Set Char
spaceSet =
  S.fromList " "

{-# INLINE newlineSet #-}
newlineSet :: S.Set Char
newlineSet =
  S.fromList "\n"

{-# INLINE nonSymbolSet #-}
nonSymbolSet :: S.Set Char
nonSymbolSet =
  S.fromList $ "() \"\n;,"

{-# INLINE nonSimpleSymbolSet #-}
nonSimpleSymbolSet :: S.Set Char
nonSimpleSymbolSet =
  S.insert '.' nonSymbolSet

-- S.fromList $ "() \"\n;."

{-# INLINE updateStreamL #-}
updateStreamL :: T.Text -> IO ()
updateStreamL s = do
  modifyIORef' text $ \_ -> s
  incrementLine

{-# INLINE updateStreamC #-}
updateStreamC :: Int -> T.Text -> IO ()
updateStreamC c s = do
  modifyIORef' text $ \_ -> s
  modifyIORef' column $ \x -> c + x

{-# INLINE incrementLine #-}
incrementLine :: IO ()
incrementLine = do
  modifyIORef' line $ \x -> 1 + x
  modifyIORef' column $ \_ -> 1

{-# INLINE incrementColumn #-}
incrementColumn :: IO ()
incrementColumn =
  modifyIORef' column $ \x -> 1 + x

raiseParseError :: T.Text -> IO a
raiseParseError txt = do
  m <- currentHint
  throw $ Error [logError (getPosInfo m) txt]

-- asKeyword :: T.Text -> Maybe Keywordみたいにすべきかも。
isKeyword :: T.Text -> Bool
isKeyword s =
  S.member s keywordSet

keywordSet :: S.Set T.Text
keywordSet =
  S.fromList
    [ "-",
      "->",
      ".",
      "=",
      ":",
      "define",
      "derangement",
      "else",
      "end",
      "idealize",
      "if",
      "in",
      "lambda",
      "let",
      "let?",
      "match",
      "match-noetic",
      "new",
      "over",
      "pi",
      "question",
      "switch",
      "tau",
      "then",
      "with"
    ]

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
