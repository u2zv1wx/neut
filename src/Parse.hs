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
import Data.Maybe

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

parseV :: Parser V
parseV =
  try parseVSym <|> try (parseParen parseVNotation) <|> parseParen parseV'

parseE :: Parser E
parseE =
  try parseESym <|> try (parseParen parseENotation) <|> parseParen parseE'

parseV' :: Parser V
parseV' =
  try parseVConsApp <|> try parseLAM <|> try parseZETA <|> try parseAPPZETA <|>
  try parseThunk <|>
  try parseFORCE <|>
  try parseVAsc <|>
  parseAPP

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

parseVNotation :: Parser V
parseVNotation = do
  head <- lookAhead symbol
  env <- get
  let nameList = map (\(s, _, v) -> s) (vNotationEnv env)
  if head `elem` nameList
    then fail $ "The notation " ++ show head ++ " is not defined"
    else do
      v <- parseV'
      expandNotationV v

parseENotation :: Parser E
parseENotation = do
  head <- lookAhead symbol
  env <- get
  let nameList = map (\(s, _, v) -> s) (eNotationEnv env)
  if head `elem` nameList
    then fail $ "The notation " ++ show head ++ " is not defined"
    else do
      e <- parseE'
      expandNotationE e

-- expand all the occurrence of macros in v, recursively
expandNotationV :: V -> Parser V
expandNotationV v = do
  env <- get
  let venv = vNotationEnv env
  msubst <- findMatchV venv v
  case msubst of
    Nothing -> return v
    Just sub -> do
      v' <- substV sub v
      expandNotationV v

expandNotationE :: E -> Parser E
expandNotationE e = do
  env <- get
  let eenv = eNotationEnv env
  msubst <- findMatchE eenv e
  case msubst of
    Nothing -> return e
    Just sub -> do
      e' <- substE sub e
      expandNotationE e

findMatchV :: [(String, Form, V)] -> V -> Parser (Maybe Subst)
findMatchV [] _ = return Nothing
findMatchV ((s, f, _):vs) v = do
  case unifyFormV f v of
    Left _ -> findMatchV vs v
    Right sub -> return $ Just sub

findMatchE :: [(String, Form, E)] -> E -> Parser (Maybe Subst)
findMatchE [] _ = return Nothing
findMatchE ((s, f, _):vs) e = do
  case unifyFormE f e of
    Left _ -> findMatchE vs e
    Right sub -> return $ Just sub

type Subst = ([(String, Term)], Maybe [Term])

substTerm :: Subst -> Term -> Parser Term
substTerm sub (PosTerm t) = PosTerm <$> substV sub t
substTerm sub (NegTerm t) = NegTerm <$> substE sub t

type DidSubst = Bool

substV :: Subst -> V -> Parser V
substV (sub, _) (VPosSym (PosSym (S sym))) =
  case lookup sym sub of
    Nothing -> return (VPosSym (PosSym (S sym)))
    Just t ->
      case termToValue t of
        Nothing -> fail $ "Polarity mismatch: " ++ show t
        Just v -> return v
substV s (VConsApp c ts) = VConsApp c <$> mapM (substTerm s) ts
substV (sub, Just rest) (LAM ns v) = do
  let ns' = concatAtTailESym rest ns
  let ns'' = fromMaybe ns ns'
  v' <- substV (sub, Just rest) v
  return $ LAM ns'' v'
substV (sub, Nothing) (LAM ns v) = LAM ns <$> substV (sub, Nothing) v
substV (sub, Just rest) (APP v es) = do
  let es' = concatAtTailE rest es
  let es'' = fromMaybe es es'
  es''' <- mapM (substE (sub, Just rest)) es''
  v' <- substV (sub, Just rest) v
  return $ APP v' es'''
substV s (APP v es) = do
  v' <- substV s v
  es' <- mapM (substE s) es
  return $ APP v' es'
substV s (ZETA nsym ps) = do
  vs <- mapM (substV s . snd) ps
  let ps' = zip (map fst ps) vs
  return $ ZETA nsym ps'
substV s (APPZETA e v) = do
  e' <- substE s e
  v' <- substV s v
  return $ APPZETA e' v'
substV s (Thunk e) = Thunk <$> substE s e
substV s (FORCE e) = FORCE <$> substE s e
substV s (VAsc v t) = do
  v' <- substV s v
  return $ VAsc v' t

substE :: Subst -> E -> Parser E
substE (sub, _) (ENegSym (NegSym (S sym))) =
  case lookup sym sub of
    Nothing -> return $ ENegSym (NegSym (S sym))
    Just t ->
      case termToExpr t of
        Nothing -> fail $ "Polarity mismatch: " ++ show t
        Just e -> return e
substE s (EConsApp c ts) = EConsApp c <$> mapM (substTerm s) ts
substE (sub, Just rest) (Lam xs e) = do
  let xs' = concatAtTailVSym rest xs
  let xs'' = fromMaybe xs xs'
  e' <- substE (sub, Just rest) e
  return $ Lam xs'' e'
substE (sub, Nothing) (Lam xs e) = Lam xs <$> substE (sub, Nothing) e
substE (sub, Just rest) (App e vs) = do
  let vs' = concatAtTailV rest vs
  let vs'' = fromMaybe vs vs'
  vs''' <- mapM (substV (sub, Just rest)) vs''
  e' <- substE (sub, Just rest) e
  return $ App e' vs'''
substE s (App e vs) = do
  e' <- substE s e
  vs' <- mapM (substV s) vs
  return $ App e' vs'
substE s (Zeta psym as) = do
  vs <- mapM (substE s . snd) as
  let ps' = zip (map fst as) vs
  return $ Zeta psym ps'
substE s (AppZeta v e) = do
  v' <- substV s v
  e' <- substE s e
  return $ AppZeta v' e'
substE s (THUNK v) = THUNK <$> substV s v
substE s (Force v) = Force <$> substV s v
substE s (EAsc e t) = do
  e' <- substE s e
  return $ EAsc e' t

termToExpr :: Term -> Maybe E
termToExpr (NegTerm e) = return e
termToExpr v = Nothing

termToNegSym :: Term -> Maybe NegSym
termToNegSym (NegTerm (ENegSym ns)) = return ns
termToNegSym _ = Nothing

termToPosSym :: Term -> Maybe PosSym
termToPosSym (PosTerm (VPosSym ns)) = return ns
termToPosSym _ = Nothing

termToValue :: Term -> Maybe V
termToValue (PosTerm v) = return v
termToValue e = Nothing

concatAtTailV :: [Term] -> [V] -> Maybe [V]
concatAtTailV _ [] = Nothing
concatAtTailV rest [VPosSym (PosSym (S "..."))] = do
  rest' <- mapM termToValue rest
  Just rest'
concatAtTailV rest (e:es) = do
  es' <- concatAtTailV rest es
  return (e : es)

concatAtTailE :: [Term] -> [E] -> Maybe [E]
concatAtTailE _ [] = Nothing
concatAtTailE rest [ENegSym (NegSym (S "..."))] = do
  rest' <- mapM termToExpr rest
  Just rest'
concatAtTailE rest (e:es) = do
  es' <- concatAtTailE rest es
  return (e : es)

concatAtTailESym :: [Term] -> [NegSym] -> Maybe [NegSym]
concatAtTailESym _ [] = Nothing
concatAtTailESym rest [NegSym (S "...")] = do
  rest' <- mapM termToNegSym rest
  Just rest'
concatAtTailESym rest (e:es) = do
  es' <- concatAtTailESym rest es
  return (e : es)

concatAtTailVSym :: [Term] -> [PosSym] -> Maybe [PosSym]
concatAtTailVSym _ [] = Nothing
concatAtTailVSym rest [PosSym (S "...")] = do
  rest' <- mapM termToPosSym rest
  Just rest'
concatAtTailVSym rest (e:es) = do
  es' <- concatAtTailVSym rest es
  return (e : es)

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

parseVNotationDef :: Parser ()
parseVNotationDef = do
  char '(' >> spaces >> string "notation"
  spaces1
  name <- symbol
  spaces1
  clauseList <- sepEndBy1 (parseParen parseClauseV) spaces1
  let symbolList = map (\(s, _, _) -> s) clauseList
  if not (all (\s -> s == name) symbolList)
    then fail $ "Illegal head symbol for " ++ show name
    else do
      modify (\env -> env {vNotationEnv = clauseList ++ vNotationEnv env})
      spaces >> char ')'
      return ()

parseENotationDef :: Parser ()
parseENotationDef = do
  char '(' >> spaces >> string "notation"
  spaces1
  name <- symbol
  spaces1
  clauseList <- sepEndBy1 (parseParen parseClauseE) spaces1
  let symbolList = map (\(s, _, _) -> s) clauseList
  if not (all (\s -> s == name) symbolList)
    then fail $ "Illegal head symbol for " ++ show name
    else do
      modify (\env -> env {eNotationEnv = clauseList ++ eNotationEnv env})
      spaces >> char ')'
      return ()

parseClauseE :: Parser (String, Form, E)
parseClauseE = do
  (sym, form) <- parseParen (parseFormRest <|> parseFormNoRest)
  spaces1
  body <- parseE
  return (sym, form, body)

parseClauseV :: Parser (String, Form, V)
parseClauseV = do
  (sym, form) <- parseParen (parseFormRest <|> parseFormNoRest)
  spaces1
  body <- parseV
  return (sym, form, body)

parseFormNoRest :: Parser (String, Form)
parseFormNoRest = do
  head <- symbol
  spaces
  args <- sepEndBy parseWeakForm spaces1
  spaces
  return (head, Form head args)

parseFormRest :: Parser (String, Form)
parseFormRest = do
  head <- symbol
  spaces
  args <- sepEndBy parseWeakForm spaces1
  string "..." >> spaces
  return (head, FormWithRest head args)

parseWeakForm :: Parser WeakForm
parseWeakForm = try parseWeakFormHoleOrSymbol <|> parseParen parseWeakFormApp

parseWeakFormHoleOrSymbol :: Parser WeakForm
parseWeakFormHoleOrSymbol = do
  ms <- parseSymbol
  case ms of
    Hole -> return WeakFormHole
    S s -> do
      return $ WeakFormSymbol s

parseWeakFormApp :: Parser WeakForm
parseWeakFormApp = do
  head <- parseWeakForm
  spaces
  args <- sepEndBy parseWeakForm spaces1
  return $ WeakFormApp head args

parseReserved :: Parser ()
parseReserved = do
  string "reserved" >> spaces1
  s <- symbol
  modify (\env -> env {reservedEnv = s : reservedEnv env})
