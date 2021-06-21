module Parse.WeakTerm where

import Codec.Binary.UTF8.String
import Control.Monad (forM)
import Data.Basic
import Data.Global
import Data.IORef
import Data.LowType
import Data.Namespace
import qualified Data.Text as T
import Data.WeakTerm
import Parse.Core
import qualified System.Info as System
import Text.Read (readMaybe)

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
    Just "array-introduction" ->
      weakTermArrayIntro
    _ ->
      tryPlanList
        [ weakTermArrow,
          weakTermAux
        ]

weakTermTau :: IO WeakTermPlus
weakTermTau = do
  m <- currentHint
  token "tau"
  return (m, WeakTermTau)

weakTermAdmitQuestion :: IO WeakTermPlus
weakTermAdmitQuestion = do
  m <- currentHint
  token "?admit"
  h <- newAster m
  return
    ( m,
      WeakTermQuestion
        ( m,
          WeakTermPiElim
            (weakVar m "os.exit")
            [ h,
              (m, WeakTermInt (m, WeakTermConst "i64") 1)
            ]
        )
        h
    )

weakTermAdmit :: IO WeakTermPlus
weakTermAdmit = do
  m <- currentHint
  token "admit"
  h <- newAster m
  return
    ( m,
      WeakTermPiElim
        (weakVar m "os.exit")
        [ h,
          (m, WeakTermInt (m, WeakTermConst "i64") 1)
        ]
    )

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
  e <- tryPlanList [weakTermDotBind, weakTermDoEnd]
  -- char '.' >> skip
  -- e <- weakTerm
  return (m, WeakTermPiIntro OpacityTransparent LamKindNormal varList e)

weakTermDotBind :: IO WeakTermPlus
weakTermDotBind = do
  char '.' >> skip
  e <- weakTerm
  return e

weakTermDoEnd :: IO WeakTermPlus
weakTermDoEnd = do
  token "do"
  e <- weakTerm
  token "end"
  return e

weakTermPiIntroFix :: IO WeakTermPlus
weakTermPiIntroFix = do
  m <- currentHint
  token "fix"
  self <- weakIdentPlus
  varList <- many weakIdentPlus
  e <- tryPlanList [weakTermDotBind, weakTermDoEnd]
  -- char '.' >> skip
  -- e <- weakTerm
  return (m, WeakTermPiIntro OpacityTransparent (LamKindFix self) varList e)

weakTermAux :: IO WeakTermPlus
weakTermAux = do
  m <- currentHint
  e <- weakTermSimple
  es <- many weakTermSimple
  if null es
    then return e
    else return (m, WeakTermPiElim e es)

weakTermArrow :: IO WeakTermPlus
weakTermArrow = do
  m <- currentHint
  xt <- weakTermArrowItem
  xts <- many1 $ (token "->" >> weakTermArrowItem)
  let (_, _, cod) = last xts
  return (m, WeakTermPi (xt : init xts) cod)

weakTermArrowItem :: IO WeakIdentPlus
weakTermArrowItem = do
  tryPlanList
    [ weakAscription,
      do
        m <- currentHint
        a <- tryPlanList [weakTermAux, weakTermTau, weakTermVar]
        h <- newIdentFromText "_"
        return (m, h, a)
    ]

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

weakTermDerangement :: IO WeakTermPlus
weakTermDerangement = do
  m <- currentHint
  token "derangement"
  k <- tryPlanList [weakTermDerangementNop, betweenParen weakTermDerangementKind]
  es <- many weakTermSimple
  return (m, WeakTermDerangement k es)

weakTermDerangementNop :: IO Derangement
weakTermDerangementNop = do
  token "nop"
  return DerangementNop

weakTermDerangementKind :: IO Derangement
weakTermDerangementKind = do
  m <- currentHint
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
      raiseParseError m "invalid derangement kind"

weakTermDerangementKind' :: IO Derangement
weakTermDerangementKind' = do
  m <- currentHint
  headSymbol <- symbol
  case headSymbol of
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
      raiseParseError m "invalid derangement kind"

-- t ::= i{n} | f{n} | pointer t | array INT t | struct t ... t
lowType :: IO LowType
lowType = do
  m <- currentHint
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
        raiseParseError m "lowType"

lowTypeSimple :: IO LowType
lowTypeSimple = do
  tryPlanList
    [ betweenParen lowType,
      lowTypeInt,
      lowTypeFloat
    ]

lowTypeInt :: IO LowType
lowTypeInt = do
  m <- currentHint
  headSymbol <- symbol
  case asLowInt headSymbol of
    Just size ->
      return $ LowTypeInt size
    Nothing ->
      raiseParseError m "lowTypeInt"

lowTypeFloat :: IO LowType
lowTypeFloat = do
  m <- currentHint
  headSymbol <- symbol
  case asLowFloat headSymbol of
    Just size ->
      return $ LowTypeFloat size
    Nothing ->
      raiseParseError m "lowTypeFloat"

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
  c <- symbol
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
  t1 <- newAster m
  resultType <- newAster m
  return
    ( m,
      WeakTermPiElim
        (m, WeakTermVar VarKindLocal (asIdent "identity.bind"))
        [ t1,
          resultType,
          e1,
          (m, WeakTermPiIntro OpacityTransparent LamKindNormal [x] e2)
        ]
    )

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
  let sumLeft = asIdent "sum.left"
  return
    ( m,
      WeakTermCase
        (doNotCare m)
        Nothing
        (e1, doNotCare m)
        [ ( (m, sumLeft, [(m, err, typeOfLeft)]),
            (m, WeakTermPiElim (m, WeakTermVar VarKindLocal sumLeft) [typeOfLeft, typeOfRight, (m, WeakTermVar VarKindLocal err)])
          ),
          ( (m, asIdent "sum.right", [x]),
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
  elseIfList <- many weakTermElseIf
  token "else"
  e3 <- weakTerm
  token "end"
  foldIf m e1 e2 elseIfList e3

weakTermElseIf :: IO (WeakTermPlus, WeakTermPlus)
weakTermElseIf = do
  token "else-if"
  e1 <- weakTerm
  token "then"
  e2 <- weakTerm
  return (e1, e2)

foldIf :: Hint -> WeakTermPlus -> WeakTermPlus -> [(WeakTermPlus, WeakTermPlus)] -> WeakTermPlus -> IO WeakTermPlus
foldIf m e1 e2 elseIfList e3 =
  case elseIfList of
    [] -> do
      h <- newAster m
      return
        ( m,
          WeakTermEnumElim
            (e1, h)
            [ ((m, EnumCaseLabel "bool.true"), e2),
              ((m, EnumCaseLabel "bool.false"), e3)
            ]
        )
    ((elseIfCond, elseIfBody) : rest) -> do
      item <- foldIf m elseIfCond elseIfBody rest e3
      h <- newAster m
      return
        ( m,
          WeakTermEnumElim
            (e1, h)
            [ ((m, EnumCaseLabel "bool.true"), e2),
              ((m, EnumCaseLabel "bool.false"), item)
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
          [castToNoema subject t (m, WeakTermIgnore (m, WeakTermVar VarKindLocal x))] -- FIXME: ここでxをdo-not-consumeに包むべき
      )

weakTermArrayIntro :: IO WeakTermPlus
weakTermArrayIntro = do
  m <- currentHint
  token "array-introduction"
  t <- lowTypeSimple
  es <- many weakTermSimple
  arr <- newIdentFromText "arr"
  ptr <- newIdentFromText "ptr"
  h1 <- newIdentFromText "_"
  h2 <- newIdentFromText "_"
  let ptrType = weakVar m "unsafe.pointer"
  let topType = weakVar m "top"
  arrText <- lowTypeToArrayKindText m t
  let arrName = arrText <> "-array" -- e.g. i8-array
  t' <- lowTypeToWeakTerm m t
  es' <- mapM (annotate t') es
  return $
    bind m (m, arr, ptrType) (m, WeakTermDerangement (DerangementCreateArray t) es') $
      bind m (m, ptr, ptrType) (m, WeakTermPiElim (weakVar m "memory.allocate") [intTerm m 16]) $
        bind m (m, h1, topType) (m, WeakTermPiElim (weakVar m "memory.store-i64-with-index") [(weakVar m (asText ptr)), intTerm m 0, intTerm m (toInteger (length es))]) $
          bind m (m, h2, topType) (m, WeakTermPiElim (weakVar m "memory.store-pointer-with-index") [(weakVar m (asText ptr)), intTerm m 1, (weakVar m (asText arr))]) $
            (m, WeakTermPiElim (weakVar m "unsafe.cast") [weakVar m "unsafe.pointer", weakVar m arrName, weakVar m (asText ptr)])

lowTypeToWeakTerm :: Hint -> LowType -> IO WeakTermPlus
lowTypeToWeakTerm m t =
  case t of
    LowTypeInt s ->
      return (m, WeakTermConst (showIntSize s))
    LowTypeFloat s ->
      return (m, WeakTermConst (showFloatSize s))
    _ ->
      raiseParseError m "invalid argument passed to lowTypeToType"

annotate :: WeakTermPlus -> WeakTermPlus -> IO WeakTermPlus
annotate t e = do
  let m = fst e
  h <- newIdentFromText "_"
  return
    ( m,
      WeakTermPiElim
        ( m,
          WeakTermPiIntro
            OpacityTransparent
            LamKindNormal
            [(m, h, t)]
            (weakVar m (asText h))
        )
        [e]
    )

lowTypeToArrayKindText :: Hint -> LowType -> IO T.Text
lowTypeToArrayKindText m t =
  case t of
    LowTypeInt size ->
      return $ showIntSize size
    LowTypeFloat size ->
      return $ showFloatSize size
    _ -> do
      raiseParseError m "unsupported array kind"

intTerm :: Hint -> Integer -> WeakTermPlus
intTerm m i =
  (m, WeakTermInt (m, WeakTermConst "i64") i)

bind :: Hint -> WeakIdentPlus -> WeakTermPlus -> WeakTermPlus -> WeakTermPlus
bind m mxt e cont =
  (m, WeakTermPiElim (m, WeakTermPiIntro OpacityTransparent LamKindNormal [mxt] cont) [e])

--
-- term-related helper functions
--

weakTermSimple :: IO WeakTermPlus
weakTermSimple = do
  tryPlanList
    [ weakTermSigmaIntro,
      betweenParen weakTerm,
      weakTermTau,
      weakTermAster,
      weakTermString,
      weakTermInteger,
      weakTermFloat,
      weakTermBuiltin,
      weakTermAdmitQuestion,
      weakTermAdmit,
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
    then raiseParseError m $ "found a keyword `" <> x <> "`, expecting a variable"
    else return (m, asIdent x)

var :: IO (Hint, T.Text)
var = do
  m <- currentHint
  x <- symbol
  if isKeyword x
    then raiseParseError m $ "found a reserved symbol `" <> x <> "`, expecting a variable"
    else return (m, x)

varText :: IO T.Text
varText =
  snd <$> var

weakTermBuiltin :: IO WeakTermPlus
weakTermBuiltin = do
  m <- currentHint
  x <- symbol
  case x of
    "target-platform" -> do
      target <- getTarget
      return (m, WeakTermVar VarKindLocal (asIdent $ "target" <> nsSep <> target))
    _ ->
      raiseParseError m $ "no such builtin constant: " <> x

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
              (DerangementCreateArray (LowTypeInt 8))
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
  m <- currentHint
  x <- symbol
  case readMaybe (T.unpack x) of
    Just intValue ->
      return intValue
    Nothing ->
      raiseParseError m $ "unexpected symbol: " <> x <> "\n expecting: an integer"

weakTermFloat :: IO WeakTermPlus
weakTermFloat = do
  m <- currentHint
  x <- symbol
  case readMaybe (T.unpack x) of
    Just floatValue -> do
      h <- newAster m
      return (m, WeakTermFloat h floatValue)
    Nothing ->
      raiseParseError m $ "unexpected symbol: " <> x <> "\n expecting: an integer"

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

getTarget :: IO T.Text
getTarget = do
  mx <- readIORef targetPlatform
  case mx of
    Just x ->
      return x
    Nothing ->
      return $ T.pack System.os <> "-" <> defaultTargetArch

-- cf. https://www.debian.org/ports/
defaultTargetArch :: T.Text
defaultTargetArch =
  case System.arch of
    "aarch64" ->
      "arm64"
    "x86_64" ->
      "amd64"
    other ->
      T.pack other
