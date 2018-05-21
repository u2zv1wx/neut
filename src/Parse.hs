module Parse
  ( readExpr
  ) where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans.Except

import Text.Parsec hiding (Parsec)

import Data
import Data.List

type Parser a = ParsecT String () (StateT Env (ExceptT String IO)) a

readExpr :: String -> String -> WithEnv Program
readExpr top input = do
  env <- get
  t <- runParserT parseProgram () top input
  case t of
    Left err -> lift $ throwE (show err)
    Right p -> return p

readExpr' par top input = do
  env <- get
  t <- runParserT par () top input
  case t of
    Left err -> lift $ throwE (show err)
    Right p -> return p

symbol :: Parser String
symbol = many1 (noneOf "()[] ")

spaces1 :: Parser ()
spaces1 = skipMany1 space

parseSymbol :: Parser Symbol
parseSymbol = do
  atom <- symbol
  return $
    case atom of
      "_" -> Hole
      _ -> S atom

parseParen :: Parser a -> Parser a
parseParen p = do
  char '(' >> spaces
  x <- p
  spaces >> char ')'
  return x

parsePosSym :: Parser PosSym
parsePosSym = (PosSym <$> parseSymbol) <|> parsePosAscSym

parseNegSym :: Parser NegSym
parseNegSym = (NegSym <$> parseSymbol) <|> parseNegAscSym

parseAscSym :: Parser a -> Parser b -> (a -> b -> c) -> Parser c
parseAscSym p1 p2 c = do
  string "ascribe" >> spaces1
  x <- p1
  _ <- spaces1
  p <- p2
  return $ c x p

parsePosAscSym :: Parser PosSym
parsePosAscSym =
  parseParen $ parseAscSym (PosSym <$> parseSymbol) parsePosType PosSymAsc

parseNegAscSym :: Parser NegSym
parseNegAscSym =
  parseParen $ parseAscSym (NegSym <$> parseSymbol) parseNegType NegSymAsc

parseType :: Parser Type
parseType = (PosType <$> parsePosType) <|> (NegType <$> parseNegType)

parsePosType :: Parser PosType
parsePosType =
  try parsePosUniv <|> try (PosTypeSym <$> parsePosSym) <|>
  parseParen parsePosType'

parseNegType :: Parser NegType
parseNegType =
  try parseNegUniv <|> try (NegTypeSym <$> parseNegSym) <|>
  parseParen parseNegType'

parsePosType' :: Parser PosType
parsePosType' =
  parseValueApp <|> parseCoCompApp <|> parseFORALL <|> parseSWITCH <|>
  parseClosure

parseNegType' :: Parser NegType
parseNegType' =
  (NegTypeSym <$> parseNegSym) <|> parseCoValueApp <|> parseCompApp <|>
  parseForAll <|>
  parseSwitch <|>
  parseCLOSURE

parseTConsApp :: (Env -> [TypeDef]) -> Parser (TypeDef, [Type])
parseTConsApp f = do
  s <- parseSymbol
  env <- get
  case find (\def -> specName def == s) (f env) of
    Nothing -> fail $ "The value type " ++ show s ++ " is not defined"
    Just s -> do
      args <- sepEndBy parseType spaces1
      return (s, args)

parseValueApp :: Parser PosType
parseValueApp = do
  (v, args) <- parseParen (parseTConsApp valueTypeEnv)
  return $ ValueApp v args

parseCoValueApp :: Parser NegType
parseCoValueApp = do
  (v, args) <- parseParen (parseTConsApp valueTypeEnv)
  return $ CoValueApp v args

parseCompApp :: Parser NegType
parseCompApp = do
  (e, args) <- parseTConsApp compTypeEnv
  return $ CompApp e args

parseCoCompApp :: Parser PosType
parseCoCompApp = do
  (e, args) <- parseTConsApp compTypeEnv
  return $ CoCompApp e args

parseForAll :: Parser NegType
parseForAll = do
  string "forall"
  xts <- parseForAllArgs
  spaces1
  cod <- parseNegType
  return $ ForAll xts cod

parseFORALL :: Parser PosType
parseFORALL = do
  string "FORALL"
  xts <- parseFORALLArgs
  spaces1
  cod <- parsePosType
  return $ FORALL xts cod

parseForAllArgs :: Parser [(PosSym, PosType)]
parseForAllArgs = parseParen $ sepEndBy (parseParen parseForAllArg) spaces1

parseFORALLArgs :: Parser [(NegSym, NegType)]
parseFORALLArgs = parseParen $ sepEndBy (parseParen parseFORALLArg) spaces1

parseForAllArg :: Parser (PosSym, PosType)
parseForAllArg = parsePair parsePosSym parsePosType

parseFORALLArg :: Parser (NegSym, NegType)
parseFORALLArg = parsePair parseNegSym parseNegType

parseSwitch :: Parser NegType
parseSwitch = do
  string "switch"
  spaces1
  x <- parsePosSym
  spaces1
  p <- parsePosType
  spaces1
  args <- parseParen parseSwitchArgs
  return $ Switch x p args

parseSWITCH :: Parser PosType
parseSWITCH = do
  string "SWITCH"
  spaces1
  x <- parseNegSym
  spaces1
  p <- parseNegType
  spaces1
  args <- parseParen parseSWITCHArgs
  return $ SWITCH x p args

parseSwitchArgs :: Parser [(Assertion, NegType)]
parseSwitchArgs = sepEndBy (parseParen parseSwitchArg) spaces1

parseSWITCHArgs :: Parser [(Refutation, PosType)]
parseSWITCHArgs = sepEndBy (parseParen parseSWITCHArg) spaces1

parseSwitchArg :: Parser (Assertion, NegType)
parseSwitchArg = parsePair parseAssertion parseNegType

parseSWITCHArg :: Parser (Refutation, PosType)
parseSWITCHArg = parsePair parseRefutation parsePosType

parsePair :: Parser a -> Parser b -> Parser (a, b)
parsePair p1 p2 = do
  x <- p1
  spaces1
  y <- p2
  return (x, y)

parseClosure :: Parser PosType
parseClosure = do
  string "closure" >> spaces1
  n <- parseNegType
  return $ Closure n

parseCLOSURE :: Parser NegType
parseCLOSURE = do
  string "CLOSURE" >> spaces1
  p <- parsePosType
  return $ CLOSURE p

parsePosUniv :: Parser PosType
parsePosUniv = string "positive" >> return PosUniv

parseNegUniv :: Parser NegType
parseNegUniv = string "negative" >> return NegUniv

parseProgram :: Parser Program
parseProgram = Thread <$> sepEndBy1 (parseParen parseThread) spaces1

parseThread :: Parser Term
parseThread = do
  string "thread" >> spaces1
  parseTerm

parseTerm :: Parser Term
parseTerm = (PosTerm <$> parseV) <|> (NegTerm <$> parseE)

-- (can be extended with notation)
parseV :: Parser V
parseV = try parseVSym <|> parseParen parseV'

parseV' :: Parser V
parseV' =
  try parseVConsApp <|> try parseLAM <|> try parseZETA <|> try parseAPPZETA <|>
  try parseThunk <|>
  try parseFORCE <|>
  try parseVAsc <|>
  parseAPP

parseE :: Parser E
parseE = try parseESym <|> parseParen parseE'

parseE' :: Parser E
parseE' =
  try parseEConsApp <|> try parseLam <|> try parseZeta <|> try parseAppZeta <|>
  try parseTHUNK <|>
  try parseForce <|>
  try parseEAsc <|>
  parseApp

parseVSym :: Parser V
parseVSym = VPosSym <$> parsePosSym

parseESym :: Parser E
parseESym = ENegSym <$> parseNegSym

parseConsApp :: (ConsDef -> [Term] -> a) -> Parser a
parseConsApp consapp = do
  s <- parseSymbol
  env <- get
  case find (\def -> consName def == s) (consEnv env) of
    Nothing -> fail $ "The constructor " ++ show s ++ " is not defined"
    Just def -> consapp def <$> sepEndBy parseTerm spaces1

parseVConsApp :: Parser V
parseVConsApp = parseConsApp VConsApp

parseEConsApp :: Parser E
parseEConsApp = parseConsApp EConsApp

parseLam :: Parser E
parseLam = do
  string "lambda" >> spaces1
  args <- parseLamArg
  spaces1
  e <- parseE
  return $ Lam args e

parseLAM :: Parser V
parseLAM = do
  string "LAMBDA" >> spaces1
  args <- parseLAMArg
  spaces1
  v <- parseV
  return $ LAM args v

parseLamArg :: Parser [PosSym]
parseLamArg = parseParen $ sepEndBy1 parsePosSym spaces1

parseLAMArg :: Parser [NegSym]
parseLAMArg = parseParen $ sepEndBy1 parseNegSym spaces1

parseApp :: Parser E
parseApp = do
  e <- parseE
  spaces1
  vs <- sepEndBy1 parseV spaces1
  return $ App e vs

parseAPP :: Parser V
parseAPP = do
  v <- parseV
  spaces1
  es <- sepEndBy1 parseE spaces1
  return $ APP v es

parseZeta :: Parser E
parseZeta = do
  string "zeta" >> spaces1
  x <- parsePosSym
  spaces1
  args <- sepEndBy (parseParen parseZetaArg) spaces1
  return $ Zeta x args

parseZETA :: Parser V
parseZETA = do
  string "ZETA" >> spaces1
  x <- parseNegSym
  spaces1
  args <- sepEndBy (parseParen parseZETAArg) spaces1
  return $ ZETA x args

parseZetaArg :: Parser (Assertion, E)
parseZetaArg = parsePair parseAssertion parseE

parseZETAArg :: Parser (Refutation, V)
parseZETAArg = parsePair parseRefutation parseV

parseAppZeta :: Parser E
parseAppZeta = do
  string "elim" >> spaces1
  v <- parseV
  spaces1
  e <- parseE
  return $ AppZeta v e

parseAPPZETA :: Parser V
parseAPPZETA = do
  string "ELIM" >> spaces1
  e <- parseE
  spaces1
  v <- parseV
  return $ APPZETA e v

parseThunk :: Parser V
parseThunk = do
  string "thunk" >> spaces1
  e <- parseE
  return $ Thunk e

parseTHUNK :: Parser E
parseTHUNK = do
  string "THUNK" >> spaces1
  v <- parseV
  return $ THUNK v

parseForce :: Parser E
parseForce = do
  string "force" >> spaces1
  v <- parseV
  return $ Force v

parseFORCE :: Parser V
parseFORCE = do
  string "FORCE" >> spaces1
  e <- parseE
  return $ FORCE e

parseVAsc :: Parser V
parseVAsc = do
  string "ascribe" >> spaces1
  v <- parseV
  spaces1
  p <- parsePosType
  return $ VAsc v p

parseEAsc :: Parser E
parseEAsc = do
  string "ascribe" >> spaces1
  e <- parseE
  spaces1
  n <- parseNegType
  return $ EAsc e n

parsePat :: Parser Pat
parsePat = (PosPat <$> parseAssertion) <|> (NegPat <$> parseRefutation)

parseAssertion :: Parser Assertion
parseAssertion = parseParen parsePosConsApp <|> parsePosConsApp <|> parsePosAtom

parseRefutation :: Parser Refutation
parseRefutation =
  parseParen parseNegConsApp <|> parseNegConsApp <|> parseNegAtom

parsePosAtom :: Parser Assertion
parsePosAtom = PosAtom <$> parsePosSym

parseNegAtom :: Parser Refutation
parseNegAtom = NegAtom <$> parseNegSym

parsePosConsApp :: Parser Assertion
parsePosConsApp = do
  s <- parseSymbol
  env <- get
  case find (\def -> consName def == s) (consEnv env) of
    Nothing -> fail $ "The constructor " ++ show s ++ " is not defined"
    Just def@ConsDef {consArg = args} ->
      if null args
        then return $ PosConsApp def []
        else PosConsApp def <$> sepEndBy parsePat spaces1

parseNegConsApp :: Parser Refutation
parseNegConsApp = do
  s <- parseSymbol
  env <- get
  case find (\def -> consName def == s) (consEnv env) of
    Nothing -> fail $ "The constructor " ++ show s ++ " is not defined"
    Just def@ConsDef {consArg = args} ->
      if null args
        then return $ NegConsApp def []
        else NegConsApp def <$> sepEndBy parsePat spaces1

parseDefArg :: Parser (Symbol, Type)
parseDefArg = parsePair parseSymbol parseType

parseValueDef :: Parser ValueDef
parseValueDef =
  parseDef
    "value"
    (\def -> modify (\env -> env {valueTypeEnv = def : valueTypeEnv env}))

parseCompDef :: Parser CompDef
parseCompDef =
  parseDef
    "computation"
    (\def -> modify (\env -> env {compTypeEnv = def : compTypeEnv env}))

parseDef :: String -> (TypeDef -> Parser ()) -> Parser TypeDef
parseDef name updater = do
  char '(' >> spaces >> string name
  spaces1
  s <- parseSymbol
  spaces
  args <- sepEndBy (parseParen parseDefArg) spaces1
  spaces >> char ')'
  let def = TypeDef {specName = s, specArg = args}
  updater def
  return def

parseConsDef :: Parser ConsDef
parseConsDef = do
  char '(' >> spaces >> string "constructor"
  spaces1
  name <- parseSymbol
  spaces1
  args <- parseParen $ sepEndBy (parseParen parseDefArg) spaces1
  spaces
  cod <- parseType
  spaces >> char ')'
  let consDef = ConsDef {consName = name, consArg = args, consCod = cod}
  modify (\env -> env {consEnv = consDef : consEnv env})
  return consDef

parseVNotation :: Parser VNotation
parseVNotation = do
  char '(' >> spaces >> string "notation"
  spaces1
  name <- parseSymbol
  spaces1
  form <- parseParen parseForm
  spaces1
  body <- parseV
  let notation =
        VNotation
          {vNotationName = name, vNotationForm = form, vNotationBody = body}
  modify (\env -> env {vNotationEnv = notation : vNotationEnv env})
  spaces >> char ')'
  return notation

parseENotation :: Parser ENotation
parseENotation = do
  char '(' >> spaces >> string "notation"
  spaces1
  name <- parseSymbol
  spaces1
  form <- parseParen parseForm
  spaces1
  body <- parseE
  let notation =
        ENotation
          {eNotationName = name, eNotationForm = form, eNotationBody = body}
  modify (\env -> env {eNotationEnv = notation : eNotationEnv env})
  spaces >> char ')'
  return notation

parseForm :: Parser Form
parseForm = do
  head <- parseStrongForm
  spaces
  args <- sepEndBy parseWeakForm spaces1
  return $ Form head args

parseStrongForm :: Parser StrongForm
parseStrongForm = try parseStrongFormHole <|> parseParen parseStrongFormApp

parseStrongFormHole :: Parser StrongForm
parseStrongFormHole = do
  s <- parseSymbol
  case s of
    Hole -> return StrongFormHole
    _ -> fail "The head of form pattern is not a hole"

parseStrongFormApp :: Parser StrongForm
parseStrongFormApp = do
  head <- parseStrongForm
  spaces
  args <- sepEndBy parseWeakForm spaces1
  return $ StrongFormApp head args

parseWeakForm :: Parser WeakForm
parseWeakForm = try parseWeakFormHoleOrSymbol <|> parseParen parseWeakFormApp

parseWeakFormHoleOrSymbol :: Parser WeakForm
parseWeakFormHoleOrSymbol = do
  s <- parseSymbol
  case s of
    Hole -> return WeakFormHole
    sym -> return $ WeakFormSymbol sym

parseWeakFormApp :: Parser WeakForm
parseWeakFormApp = do
  head <- parseWeakForm
  spaces
  args <- sepEndBy parseWeakForm spaces1
  return $ WeakFormApp head args
