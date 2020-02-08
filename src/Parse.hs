{-# LANGUAGE OverloadedStrings #-}

module Parse
  ( parse
  , complete
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.List
import Data.Monoid ((<>))
import Data.Tuple (swap)
import Path
import Path.IO
import Text.Read (readMaybe)

import qualified Data.HashMap.Strict as Map
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Text.Show.Pretty as Pr

import Data.Basic
import Data.Env
import Data.Tree
import Data.WeakTerm
import Parse.Interpret
import Parse.MacroExpand
import Parse.Read
import Parse.Rename
import Parse.Utility

-- {} parse {the output term is correctly renamed}
-- (The postcondition is guaranteed by the assertion of `rename`.)
parse :: Path Abs File -> WithEnv WeakTermPlus
parse inputPath = do
  content <- liftIO $ TIO.readFile $ toFilePath inputPath
  stmtList <- strToTree content (toFilePath inputPath) >>= parse'
  stmtList' <- renameStmtList stmtList
  concatStmtList stmtList'

complete :: Path Abs File -> Line -> Column -> WithEnv [String]
complete inputPath l c = do
  info <- parseForCompletion inputPath l c
  return $ showCompInfo info

showCompInfo :: CompInfo -> [String]
showCompInfo [] = []
showCompInfo ((x, m):xms) = do
  case getInfo m of
    Nothing -> showCompInfo xms
    Just (path, (_, l, c)) -> do
      let pathStr = "\"" <> toFilePath path <> "\""
      let x' = T.unpack x
      let str =
            "(\"" ++
            x' ++ "\" (" ++ pathStr ++ " " ++ show l ++ " " ++ show c ++ "))"
      str : showCompInfo xms

parseForCompletion :: Path Abs File -> Line -> Column -> WithEnv CompInfo
parseForCompletion inputPath l c = do
  content <- liftIO $ TIO.readFile $ toFilePath inputPath
  s <- newNameWith "cursor"
  case modifyFileForCompletion s content l c of
    Nothing -> return []
    Just (prefix, content') -> do
      stmtList <- strToTree content' (toFilePath inputPath) >>= parse'
      case compInfo s stmtList of
        Right () -> return []
        Left info -> do
          let info' = filter (filterCompInfo prefix) info
          let compareLoc m1 m2 = metaLocation m2 `compare` metaLocation m1
          return $ nub $ sortBy (\(_, m1) (_, m2) -> compareLoc m1 m2) info'

filterCompInfo :: Prefix -> (Identifier, Meta) -> Bool
filterCompInfo prefix (x, m)
  | True <- metaIsAppropriateAsCompletionCandidate m = prefix `T.isPrefixOf` x
  | otherwise = False

type Prefix = T.Text

-- 必要ならここでprefixの情報も与える
-- parenとかのときは何も返さないからNothingにする
modifyFileForCompletion ::
     CursorName -> T.Text -> Line -> Column -> Maybe (Prefix, T.Text)
modifyFileForCompletion s content l c = do
  let xs = T.lines content
  let (ys, ws) = splitAt (fromInteger $ l - 1) xs
  (targetLine, zs) <- headTailMaybe ws
  (s1, s2) <- splitAtMaybe (c - 1) targetLine
  (ch, s2') <- headTailMaybeText s2
  case ch of
    '(' -> Nothing
    ')' -> do
      let targetLine' = s1 <> " " <> s <> s2
      return (T.empty, T.unlines $ ys ++ [targetLine'] ++ zs)
    ' ' -> do
      let targetLine' = s1 <> " " <> s <> s2
      return (T.empty, T.unlines $ ys ++ [targetLine'] ++ zs)
    _ -> do
      let baseStr = s1 <> T.singleton ch
      let revBaseStr = T.reverse baseStr
      let revPrefix = T.takeWhile (`notElem` ['(', ' ', ')']) revBaseStr
      let prefix = T.reverse revPrefix
      let revStr = T.dropWhile (`notElem` ['(', ' ', ')']) revBaseStr
      let s1' = T.reverse revStr
      let s2'' = T.dropWhile (`notElem` ['(', ' ', ')']) s2'
      let targetLine' = s1' <> s <> s2''
      return (prefix, T.unlines $ ys ++ [targetLine'] ++ zs)

headTailMaybe :: [a] -> Maybe (a, [a])
headTailMaybe [] = Nothing
headTailMaybe (x:xs) = return (x, xs)

headTailMaybeText :: T.Text -> Maybe (Char, T.Text)
headTailMaybeText s
  | s == T.empty = Nothing
  | otherwise = return (T.head s, T.tail s)

splitAtMaybe :: Integer -> T.Text -> Maybe (T.Text, T.Text)
splitAtMaybe i xs = do
  let i' = fromInteger i
  if 0 <= i' && i' < T.length xs
    then return $ T.splitAt i' xs
    else Nothing

-- {} parse' {}
-- Parse the head element of the input list.
parse' :: [TreePlus] -> WithEnv [Stmt]
parse' [] = return []
parse' ((_, TreeNode [(_, TreeAtom "notation"), from, to]):as) = do
  checkNotationSanity from
  modify (\e -> e {notationEnv = (from, to) : notationEnv e})
  parse' as
parse' ((_, TreeNode [(_, TreeAtom "keyword"), (_, TreeAtom s)]):as) = do
  checkKeywordSanity s
  modify (\e -> e {keywordEnv = S.insert s (keywordEnv e)})
  parse' as
parse' ((m, TreeNode ((_, TreeAtom "enum"):(_, TreeAtom name):ts)):as) = do
  indexList <- mapM extractIdentifier ts
  m' <- adjustPhase m
  insEnumEnv m' name indexList
  -- `constName` is a proof term that `name` is indeed an enum:
  --   enum.choice : is-enum choice
  -- example usage:
  --   print: Pi (A : Univ, prf : is-enum A, str : u8-array A). IO top
  -- This proof term is translated into the number of the contents of the corresponding enum type.
  -- Thus, `enum.choice` is, for example, translated into 2, assuming that choice = {left, right}.
  -- In the example of `print`, this integer in turn represents the length of the array `str`,
  -- which is indispensable for the system call `write`.
  let constName = "enum." <> name
  modify (\e -> e {constantEnv = S.insert constName (constantEnv e)})
  -- type constraint for constName
  -- e.g. t == is-enum @ (choice)
  isEnumType <- toIsEnumType name
  -- add `(constant enum.choice (is-enum choice))` to defList in order to insert appropriate type constraint
  let ascription = StmtConstDecl m' (m', constName, isEnumType)
  -- register the name of the constant
  modify (\env -> env {nameEnv = Map.insert constName constName (nameEnv env)})
  defList <- parse' as
  return $ ascription : defList
parse' ((_, TreeNode [(_, TreeAtom "include"), (_, TreeAtom pathString)]):as) =
  case readMaybe (T.unpack pathString) :: Maybe String of
    Nothing -> throwError' "the argument of `include` must be a string"
    Just path -> do
      oldFilePath <- gets currentFilePath
      newFilePath <- resolveFile (parent oldFilePath) path
      b <- doesFileExist newFilePath
      if not b
        then throwError' $ "no such file: " <> T.pack (toFilePath newFilePath)
        else do
          insertPathInfo oldFilePath newFilePath
          ensureDAG
          denv <- gets fileEnv
          case Map.lookup newFilePath denv of
            Just mxs -> do
              let header = map (toStmtLetHeader newFilePath) mxs
              defList <- parse' as
              return $ header ++ defList
            Nothing -> do
              content <- liftIO $ TIO.readFile $ toFilePath newFilePath
              modify (\env -> env {currentFilePath = newFilePath})
              modify (\env -> env {phase = 1 + phase env})
              includedStmtList <- strToTree content path >>= parse'
              let mxs = toIdentList includedStmtList
              modify (\env -> env {currentFilePath = oldFilePath})
              modify (\env -> env {phase = 1 + phase env})
              modify (\env -> env {fileEnv = Map.insert newFilePath mxs denv})
              defList <- parse' as
              let footer = map (toStmtLetFooter newFilePath) mxs
              let header = map (toStmtLetHeader newFilePath) mxs
              return $ includedStmtList ++ footer ++ header ++ defList
parse' ((_, TreeNode ((_, TreeAtom "statement"):as1)):as2) = do
  defList1 <- parse' as1
  defList2 <- parse' as2
  return $ defList1 ++ defList2
parse' ((m, TreeNode [(_, TreeAtom "constant"), (mn, TreeAtom name), t]):as) = do
  t' <- macroExpand t >>= interpret
  cenv <- gets constantEnv
  if name `S.member` cenv
    then throwError' $ "the constant " <> name <> " is already defined"
    else do
      modify (\e -> e {constantEnv = S.insert name (constantEnv e)})
      defList <- parse' as
      m' <- adjustPhase m
      mn' <- adjustPhase mn
      return $ StmtConstDecl m' (mn', name, t') : defList
parse' ((m, TreeNode [(mDef, TreeAtom "definition"), name@(_, TreeAtom _), body]):as) =
  parse' $ (m, TreeNode [(mDef, TreeAtom "let"), name, body]) : as
parse' ((m, TreeNode (def@(_, TreeAtom "definition"):name@(mFun, TreeAtom _):xts@(_, TreeNode _):body:rest)):as) =
  parse' $ (m, TreeNode [def, (mFun, TreeNode (name : xts : body : rest))]) : as
parse' ((_, TreeNode ((_, TreeAtom "definition"):xds)):as) = do
  stmt <- parseDef xds
  stmtList <- parse' as
  return $ stmt : stmtList
parse' ((m, TreeNode (ind@(_, TreeAtom "inductive"):name@(mFun, TreeAtom _):xts@(_, TreeNode _):rest)):as) = do
  parse' $ (m, TreeNode [ind, (mFun, TreeNode (name : xts : rest))]) : as
parse' ((_, TreeNode ((_, TreeAtom "inductive"):ts)):as) = do
  parseConnective ts as toInductive toInductiveIntroList
parse' ((m, TreeNode (coind@(_, TreeAtom "coinductive"):name@(mFun, TreeAtom _):xts@(_, TreeNode _):rest)):as) =
  parse' $ (m, TreeNode [coind, (mFun, TreeNode (name : xts : rest))]) : as
parse' ((_, TreeNode ((_, TreeAtom "coinductive"):ts)):as) = do
  parseConnective ts as toCoinductive toCoinductiveElimList
parse' ((m, TreeNode [(_, TreeAtom "let"), xt, e]):as) = do
  m' <- adjustPhase m
  e' <- macroExpand e >>= interpret
  (mx, x, t) <- macroExpand xt >>= interpretIdentifierPlus
  defList <- parse' as
  return $ StmtLet m' (mx, x, t) e' : defList
parse' (a:as) = do
  e <- macroExpand a
  if isSpecialForm e
    then parse' $ e : as
    else do
      e'@(meta, _) <- interpret e
      name <- newNameWith "hole-parse-last"
      t <- newHole
      defList <- parse' as
      let meta' = meta {metaIsAppropriateAsCompletionCandidate = False}
      return $ StmtLet meta' (meta', name, t) e' : defList

parseDef :: [TreePlus] -> WithEnv Stmt
parseDef xds = do
  xds' <- mapM (insImplicitBegin >=> macroExpand) xds
  mxs <- mapM extractFunName xds'
  xds'' <- mapM interpretIter xds'
  return $ StmtDef $ zip mxs xds''

-- variable naming convention on parsing connectives:
--   a : the name of a formation rule, like `nat`, `list`, `stream`, etc.
--   b : the name of an introduction/elimination rule, like `zero`, `cons`, `head`, etc.
--   x : the name of an argument of a formation rule, like `A` in `list A` or `stream A`.
--   y : the name of an argument of an introduction/elimination rule, like `w` or `ws` in `cons : Pi (w : A, ws : list A). list A`.
parseConnective ::
     [TreePlus]
  -> [TreePlus]
  -> ([IdentifierPlus] -> [IdentifierPlus] -> Connective -> WithEnv Stmt)
  -> ([IdentifierPlus] -> Connective -> WithEnv [Stmt])
  -> WithEnv [Stmt]
parseConnective ts as f g = do
  connectiveList <- mapM parseConnective' ts
  let ats = map (ruleAsIdentPlus . formationRuleOf) connectiveList
  let bts = concatMap toInternalRuleList connectiveList
  connectiveList' <- mapM (f ats bts) connectiveList
  ruleList <- concat <$> mapM (g ats) connectiveList
  stmtList <- parse' as
  return $ connectiveList' ++ ruleList ++ stmtList

parseConnective' :: TreePlus -> WithEnv Connective
parseConnective' (m, TreeNode ((_, TreeAtom name):(_, TreeNode xts):rules)) = do
  m' <- adjustPhase m
  xts' <- mapM interpretIdentifierPlus xts
  rules' <- mapM parseRule rules
  return (m', name, xts', rules')
parseConnective' _ = throwError' "parseConnective: syntax error"

parseRule :: TreePlus -> WithEnv Rule
parseRule (m, TreeNode [(mName, TreeAtom name), (_, TreeNode xts), t]) = do
  m' <- adjustPhase m
  mName' <- adjustPhase mName
  t' <- interpret t
  xts' <- mapM interpretIdentifierPlus xts
  return (m', name, mName', xts', t')
parseRule _ = throwError' "parseRule: syntax error"

-- represent the inductive logical connective within CoC
toInductive ::
     [IdentifierPlus] -> [IdentifierPlus] -> Connective -> WithEnv Stmt
toInductive ats bts connective@(m, a, xts, _) = do
  let formationRule = formationRuleOf connective
  return $
    StmtLetInductive
      (length ats)
      m
      (ruleAsIdentPlus formationRule)
      ( m
      , WeakTermPiIntro
          xts
          ( m
          , WeakTermPi
              (ats ++ bts)
              (m, WeakTermPiElim (m, WeakTermUpsilon a) (map toVar' xts))))

toInductiveIntroList :: [IdentifierPlus] -> Connective -> WithEnv [Stmt]
toInductiveIntroList ats (_, _, xts, rules) = do
  let bts = map ruleAsIdentPlus rules
  mapM (toInductiveIntro ats bts xts) rules

-- represent the introduction rule within CoC
toInductiveIntro ::
     [IdentifierPlus]
  -> [IdentifierPlus]
  -> [IdentifierPlus]
  -> Rule
  -> WithEnv Stmt
toInductiveIntro ats bts xts (mb, b, m, yts, cod) = do
  return $
    StmtLetInductiveIntro
      m
      (mb, b, (m, WeakTermPi (xts ++ yts) cod))
      (xts ++ yts)
      ats
      bts
      (mb, WeakTermUpsilon b)
      yts
      []
      (map (\(_, a, _) -> a) ats)

-- -- represent the coinductive logical connective within CoC
toCoinductive ::
     [IdentifierPlus] -> [IdentifierPlus] -> Connective -> WithEnv Stmt
toCoinductive ats bts c@(m, a, xts, _) = do
  let cod = (m, WeakTermPiElim (m, WeakTermUpsilon a) (map toVar' xts))
  let f = formationRuleOf c
  h <- newNameWith "cod"
  return $
    StmtLet
      m
      (ruleAsIdentPlus f) -- a : Pi xts. Univ
      (m, WeakTermPiIntro xts (m, WeakTermSigma (ats ++ bts ++ [(m, h, cod)])))

toCoinductiveElimList :: [IdentifierPlus] -> Connective -> WithEnv [Stmt]
toCoinductiveElimList ats (_, _, xts, rules) = do
  let bts = map ruleAsIdentPlus rules
  mapM (toCoinductiveElim ats bts xts) rules

-- represent the elimination rule within CoC
toCoinductiveElim ::
     [IdentifierPlus]
  -> [IdentifierPlus]
  -> [IdentifierPlus]
  -> Rule
  -> WithEnv Stmt
toCoinductiveElim ats bts xts (mb, b, m, yts, cod)
  | [yt] <- yts = do
    return $
      StmtLetCoinductiveElim
        m
        (mb, b, (m, WeakTermPi (xts ++ [yt]) cod))
        (xts ++ [yt])
        cod
        ats
        bts
        yt
        (toVar' yt)
        (m, WeakTermPiElim (mb, WeakTermUpsilon b) [toVar' yt])
        []
        (map (\(_, a, _) -> a) ats)
  | otherwise = throwError' "toCoinductiveElim"

ruleAsIdentPlus :: Rule -> IdentifierPlus
ruleAsIdentPlus (mb, b, m, xts, t) = (mb, b, (m, WeakTermPi xts t))

formationRuleOf :: Connective -> Rule
formationRuleOf = undefined

toInternalRuleList :: Connective -> [IdentifierPlus]
toInternalRuleList (_, _, _, rules) = map ruleAsIdentPlus rules

toVar' :: IdentifierPlus -> WeakTermPlus
toVar' (m, x, _) = (m, WeakTermUpsilon x)

toVar'' :: IdentifierPlus -> (WeakTermPlus, WeakTermPlus)
toVar'' (m, x, t) = ((m, WeakTermUpsilon x), t)

insImplicitBegin :: TreePlus -> WithEnv TreePlus
insImplicitBegin (m, TreeNode (xt:xts:body:rest)) = do
  let m' = fst body
  let beginBlock = (m', TreeNode ((m', TreeAtom "begin") : body : rest))
  return (m, TreeNode [xt, xts, beginBlock])
insImplicitBegin _ = throwError' "insImplicitBegin"

extractFunName :: TreePlus -> WithEnv Identifier
extractFunName (_, TreeNode ((_, TreeAtom x):_)) = return x
extractFunName (_, TreeNode ((_, TreeNode [(_, TreeAtom x), _]):_)) = return x
extractFunName _ = throwError' "extractFunName"

-- {} isSpecialForm {}
isSpecialForm :: TreePlus -> Bool
isSpecialForm (_, TreeNode [(_, TreeAtom "notation"), _, _]) = True
isSpecialForm (_, TreeNode [(_, TreeAtom "keyword"), (_, TreeAtom _)]) = True
isSpecialForm (_, TreeNode ((_, TreeAtom "enum"):(_, TreeAtom _):_)) = True
isSpecialForm (_, TreeNode [(_, TreeAtom "include"), (_, TreeAtom _)]) = True
isSpecialForm (_, TreeNode [(_, TreeAtom "constant"), (_, TreeAtom _), _]) =
  True
isSpecialForm (_, TreeNode ((_, TreeAtom "statement"):_)) = True
isSpecialForm (_, TreeNode [(_, TreeAtom "let"), _, _]) = True
isSpecialForm (_, TreeNode ((_, TreeAtom "definition"):_)) = True
isSpecialForm (_, TreeNode ((_, TreeAtom "inductive"):_)) = True
isSpecialForm (_, TreeNode ((_, TreeAtom "coinductive"):_)) = True
isSpecialForm _ = False

-- {} toIsEnumType {}
toIsEnumType :: Identifier -> WithEnv WeakTermPlus
toIsEnumType name = do
  return
    ( emptyMeta
    , WeakTermPiElim
        (emptyMeta, WeakTermConst "is-enum")
        [(emptyMeta, WeakTermEnum $ EnumTypeLabel name)])

-- {} concatStmtList {}
-- Represent the list of Stmts in the target language, using `let`.
-- (Note that `let x := e1 in e2` can be represented as `(lam x e2) e1`.)
-- これはrenameのあとで呼ばれる
concatStmtList :: [Stmt] -> WithEnv WeakTermPlus
concatStmtList [] = do
  return (emptyMeta, WeakTermEnumIntro $ EnumValueLabel "unit")
-- for test
concatStmtList [StmtLet _ _ e] = do
  return e
concatStmtList (StmtConstDecl m xt:es) = do
  cont <- concatStmtList es
  return (m, WeakTermConstDecl xt cont)
concatStmtList (StmtLet m xt e:es) = do
  cont <- concatStmtList es
  return (m, WeakTermPiElim (emptyMeta, WeakTermPiIntro [xt] cont) [e])
concatStmtList (StmtDef xds:ss) = do
  let ds = map snd xds
  let baseSub = map defToSub ds
  let nTimes = length baseSub
  let sub = selfCompose nTimes baseSub
  let varList = map (\(_, (m, x, _), _, _) -> (m, WeakTermUpsilon x)) ds
  let iterList = map (substWeakTermPlus sub) varList
  -- StmtLetに帰着
  let letList = toLetList $ zip xds iterList
  concatStmtList $ letList ++ ss
concatStmtList (StmtLetInductive n m xt e:es) = do
  insForm n xt e
  cont <- concatStmtList es
  return (m, WeakTermPiElim (emptyMeta, WeakTermPiIntro [xt] cont) [e])
concatStmtList (StmtLetCoinductive n m xt e:es) = do
  insForm n xt e
  cont <- concatStmtList es
  return (m, WeakTermPiElim (emptyMeta, WeakTermPiIntro [xt] cont) [e])
concatStmtList (StmtLetInductiveIntro m bt xtsyts ats bts bInner args info as:ss) = do
  args' <-
    mapM (\(e, te) -> psi ModeInternalize info [] (ats ++ bts) te e) $
    map toVar'' args -- internalize
  let s =
        StmtLet
          m
          bt
          ( m
          , WeakTermPiIntro
              xtsyts
              ( m
              , WeakTermPiIntro
                  (ats ++ bts) -- ats = [list : (...)], bts = [nil : Pi (yts). list A, cons : (...)]
                  (m, WeakTermPiElim bInner args')))
  insInductive as bt -- register the constructor (if necessary)
  concatStmtList $ s : ss
concatStmtList (StmtLetCoinductiveElim m bt xtsyt cod ats bts yt e1 e2 info as:ss) = do
  e2' <- psi ModeExternalize [] info (ats ++ bts) cod e2 -- externalize
  let s =
        StmtLet
          m
          bt
          ( m
          , WeakTermPiIntro
              xtsyt
              (m, WeakTermSigmaElim cod (ats ++ bts ++ [yt]) e1 e2'))
  insCoinductive as bt -- register the destructor (if necessary)
  concatStmtList $ s : ss

insForm :: Int -> IdentifierPlus -> WeakTermPlus -> WithEnv ()
insForm 1 (_, a, _) e =
  modify (\env -> env {formationEnv = Map.insert a (Just e) (formationEnv env)})
insForm _ (_, a, _) _ =
  modify (\env -> env {formationEnv = Map.insert a Nothing (formationEnv env)})

insInductive :: [Identifier] -> IdentifierPlus -> WithEnv ()
insInductive [a] bt = do
  ienv <- gets inductiveEnv
  modify
    (\env -> env {inductiveEnv = Map.insertWith optConcat a (Just [bt]) ienv})
insInductive as _ = do
  forM_ as $ \a -> do
    modify
      (\env -> env {inductiveEnv = Map.insert a Nothing (inductiveEnv env)})

insCoinductive :: [Identifier] -> IdentifierPlus -> WithEnv ()
insCoinductive [a] bt = do
  cenv <- gets coinductiveEnv
  modify
    (\env -> env {coinductiveEnv = Map.insertWith optConcat a (Just [bt]) cenv})
insCoinductive as _ = do
  forM_ as $ \a -> do
    modify
      (\env -> env {coinductiveEnv = Map.insert a Nothing (coinductiveEnv env)})

optConcat :: Maybe [a] -> Maybe [a] -> Maybe [a]
optConcat mNew mOld = do
  mNew' <- mNew
  mOld' <- mOld
  -- insert mNew at the end of the list (to respect the structure of ind/coind represented as pi/sigma)
  return $ mOld' ++ mNew'

-- toInductiveIntro ats bts xts (mb, b, m, yts, cod) = do
--   return $
--     StmtLet
--       m
--       (mb, b, (m, WeakTermPi (xts ++ yts) cod)) -- e.g. cons : Pi (A : tau, w : A, ws : list A). list A,
--                                                 -- where b = cons, xts = [A : tau], yts = [w : A, ws : list A], cod = list A
--       ( m
--       , WeakTermPiIntro
--           (xts ++ yts)
--           -- list A = (lam (A : Tau). Pi (list : (...), nil : (...), cons : (...)). list A) @ A
--           --        = Pi (list : (...), nil : (...), cons : (...)). list A
--           ( m
--           , WeakTermPiIntro
--               (ats ++ bts) -- ats = [list : (...)],
--                            -- bts = [nil : Pi (yts). list A, cons : (...)]
--               (m, WeakTermPiElim (mb, WeakTermUpsilon b) (map toVar' yts)) -- nil @ yts : list A
--                                                                            -- (note that the `nil` here doesn't have xts as arguments)
--            ))
-- concatStmtList (StmtCoinductive {}:_) = undefined
-- toCoinductiveElim ats bts xts (m, (mb, b), yts, cod)
--   | length yts > 0 = do
--     return $
--       StmtLet
--         m
--         (mb, b, (m, WeakTermPi (xts ++ yts) cod)) -- tail : Pi (A : tau, s : stream A). stream A
--         ( m
--         , WeakTermPiIntro
--             (xts ++ yts)
--             -- stream A = (lam (A : Tau). Sigma (stream : (...), head : (...), tail : (...)). stream A) @ A
--             --          = Sigma (list : (...), head : (...), tail : (...)). stream A
--             -- ats = [list : (...)]
--             -- bts = [head : (...), tail : Pi (y1 : stream A). stream A]
--             -- (head yts : stream A)
--             -- ~> ats ++ bts ++ [head yts] = [list : (...), head : (...), tail : Pi (y1 : stream A). stream A, y1 : stream A]
--             ( m
--             , WeakTermSigmaElim
--                 cod -- sigmaElimの型の部分はelimの結果の型。変数（yts）を同一名の変数（yts）でsubstするので依存の処理の心配もなし。
--                 -- 同一の変数名を使うのがポイント。head yts : a @ (e1, ..., en)なので、
--                 -- (1)のほうのhead ytsの型に出現するaは(1)の行のatsによって束縛されたものとなり、
--                 -- (2)のほうのhead ytsの方に出現するaは外側のtoCoinductiveの結果によって定義されたものとなる。
--                 -- 別に異なる名前を両者に与えてもよいが、同一の名前を使ったほうが実装がラクなのでこちらをとることにする。
--                 (ats ++ bts ++ [head yts]) -- (1)
--                 (toVar' $ head yts) -- (2)
--                 (m, WeakTermPiElim (mb, WeakTermUpsilon b) (map toVar' yts))))
--   | otherwise =
--     throwError'
--       "toCoinductiveElim: the antecedant of an elimination rule cannot be empty"
data Mode
  = ModeInternalize
  | ModeExternalize

flipMode :: Mode -> Mode
flipMode ModeInternalize = ModeExternalize
flipMode ModeExternalize = ModeInternalize

psi ::
     Mode
  -> [(Identifier, Identifier)] -- out ~> in (substitution {x1 := x1', ..., xn := xn'})
  -> [(Identifier, Identifier)] -- in ~> out
  -> [IdentifierPlus] -- ats ++ bts
  -> WeakTermPlus -- a type `A`
  -> WeakTermPlus -- a term `e` of type `A`
  -> WithEnv WeakTermPlus -- a term of type `A{x1 := x1', ..., xn := xn'}`
psi m isub csub atsbts t e = do
  ienv <- gets inductiveEnv
  cenv <- gets coinductiveEnv
  case t of
    (_, WeakTermPi xts cod) -> do
      let (ms, xs, ts) = unzip3 xts
      let vs = map toVar' xts
      let isub' = map swap isub
      let csub' = map swap csub
      -- backward conversion to create (A', ..., A') -> (A, ..., A)
      vs' <- zipWithM (psi (flipMode m) isub' csub' atsbts) ts vs
      let app = (fst e, WeakTermPiElim e vs')
      -- forward conversion to create B -> B'
      app' <- psi m isub csub atsbts cod app
      let ts' = map (substWeakTermPlus undefined) ts
      let xts' = zip3 ms xs ts'
      -- return (A' ..., A') -> (A, ..., A) -> B -> B'
      return $ (fst e, WeakTermPiIntro xts' app')
    (_, WeakTermPiElim va@(ma, WeakTermUpsilon a) es)
      -- ordinary internalization
      | Just _ <- lookup a isub -> do
        _ <- undefined isub (concatMap varWeakTermPlus es) -- sanity check
        return (fst e, WeakTermPiElim e (map toVar' atsbts))
      -- nested inductive type
      | Just (Just bts) <- Map.lookup a ienv -> do
        let es' = map (substWeakTermPlus undefined) es
        (xts, btsInner) <- lookupInductive a
        let a' = (ma, WeakTermPiIntro xts (ma, WeakTermPiElim va es'))
        args <- zipWithM (toInternalizedArg m isub csub atsbts es') bts btsInner
        return (fst e, WeakTermPiElim e (a' : args))
      -- invalid nested inductive type
      | Just Nothing <- Map.lookup a ienv ->
        throwError' $
        "mutual inductive type `" <>
        a <> "` cannot be used to construct a nested inductive type"
      -- ordinary externalization
      | Just _ <- lookup a csub -> do
        _ <- undefined isub (concatMap varWeakTermPlus es) -- sanity check
        x <- newNameWith "psi"
        let sigmaType = (fst e, WeakTermSigma (atsbts ++ [(fst t, x, t)]))
        return (fst e, WeakTermSigmaIntro sigmaType (map toVar' atsbts ++ [e]))
      -- nested coinductive type
      | Just (Just _) <- Map.lookup a cenv -> undefined
      -- invalid nested coinductive type
      | Just Nothing <- Map.lookup a cenv ->
        throwError' $
        "mutual coinductive type `" <>
        a <> "` cannot be used to construct a nested coinductive type"
    (_, WeakTermSigma _) -> undefined
    _ ->
      if undefined isub (varWeakTermPlus t)
        then return e
        else undefined

lookupInductive :: Identifier -> WithEnv ([IdentifierPlus], [IdentifierPlus])
lookupInductive a = do
  fenv <- gets formationEnv
  case Map.lookup a fenv of
    Just (Just (_, WeakTermPiIntro xts (_, WeakTermPi atsbts (_, WeakTermPiElim (_, WeakTermUpsilon _) _)))) -> do
      let bts = tail atsbts -- this is valid since a is not mutual
      return (xts, bts)
    Just (Just _) ->
      throwError' $
      "[compiler bug] malformed inductive type (Parse.lookupInductive)"
    Just Nothing ->
      throwError' $
      "the inductive type `" <> a <> "` must be a non-mutual inductive type"
    Nothing ->
      throwError' $ "[compiler bug] no such inductive type defined: " <> a

toInternalizedArg ::
     Mode
  -> [(Identifier, Identifier)]
  -> [(Identifier, Identifier)]
  -> [IdentifierPlus]
  -> [WeakTermPlus]
  -> IdentifierPlus
  -> IdentifierPlus
  -> WithEnv WeakTermPlus
toInternalizedArg mode isub csub atsbts es' b (mbInner, _, (_, WeakTermPi yts _)) = do
  yts' <- mapM modifyArgs yts
  args <- mapM (internalize mode isub csub atsbts) yts'
  return (mbInner, WeakTermPiElim (toVar' b) (es' ++ args))
toInternalizedArg _ _ _ _ _ _ _ = throwError' "toInternalizedArg"

modifyArgs :: IdentifierPlus -> WithEnv IdentifierPlus
modifyArgs = undefined

internalize ::
     Mode
  -> [(Identifier, Identifier)]
  -> [(Identifier, Identifier)]
  -> [IdentifierPlus]
  -> IdentifierPlus
  -> WithEnv WeakTermPlus
internalize mode isub csub atsbts (m, y, t) =
  psi mode isub csub atsbts t (m, WeakTermUpsilon y)

toLetList :: [(IdentDef, WeakTermPlus)] -> [Stmt]
toLetList [] = []
toLetList (((x, (m, (mx, _, t), _, _)), iter):rest) =
  StmtLet m (mx, x, t) iter : toLetList rest

defToSub :: Def -> (Identifier, WeakTermPlus)
defToSub (m, (mx, x, t), xts, e) = (x, (m, WeakTermIter (mx, x, t) xts e))

selfCompose :: Int -> SubstWeakTerm -> SubstWeakTerm
selfCompose 0 sub = sub
selfCompose n sub = do
  let sub' = selfCompose (n - 1) sub
  compose sub sub'

compose :: SubstWeakTerm -> SubstWeakTerm -> SubstWeakTerm
compose s1 s2 = do
  let domS2 = map fst s2
  let codS2 = map snd s2
  let codS2' = map (substWeakTermPlus s1) codS2
  let s1' = filter (\(ident, _) -> ident `notElem` domS2) s1
  s1' ++ zip domS2 codS2'

-- {} newHole {}
newHole :: WithEnv WeakTermPlus
newHole = do
  h <- newNameWith "hole-parse-zeta"
  return (emptyMeta, WeakTermZeta h)

-- {} checkKeywordSanity {}
checkKeywordSanity :: Identifier -> WithEnv ()
checkKeywordSanity "" = throwError' "empty string for a keyword"
checkKeywordSanity x
  | T.last x == '+' = throwError' "A +-suffixed name cannot be a keyword"
checkKeywordSanity _ = return ()

-- {} insEnumEnv {}
insEnumEnv :: Meta -> Identifier -> [Identifier] -> WithEnv ()
insEnumEnv m name enumList = do
  eenv <- gets enumEnv
  let xs = Map.keys eenv ++ concat (Map.elems eenv)
  case find (`elem` xs) $ name : enumList of
    Just x ->
      throwError' $
      T.pack (showMeta m) <>
      ": " <> "the constant `" <> x <> "` is already defined"
    _ -> do
      let rev = Map.fromList $ zip enumList (repeat name)
      modify
        (\e ->
           e
             { enumEnv = Map.insert name enumList (enumEnv e)
             , revEnumEnv = rev `Map.union` (revEnumEnv e)
             })

insertPathInfo :: Path Abs File -> Path Abs File -> WithEnv ()
insertPathInfo oldFilePath newFilePath = do
  g <- gets includeGraph
  let g' = Map.insertWith (++) oldFilePath [newFilePath] g
  modify (\env -> env {includeGraph = g'})

ensureDAG :: WithEnv ()
ensureDAG = do
  g <- gets includeGraph
  m <- gets mainFilePath
  case ensureDAG' m [] g of
    Right _ -> return ()
    Left cyclicPath -> do
      throwError' $ "found cyclic inclusion:\n" <> T.pack (Pr.ppShow cyclicPath)

ensureDAG' ::
     Path Abs File
  -> [Path Abs File]
  -> IncludeGraph
  -> Either [Path Abs File] () -- cyclic path (if any)
ensureDAG' a visited g =
  case Map.lookup a g of
    Nothing -> Right ()
    Just as
      | xs <- as `intersect` visited
      , not (null xs) -> do
        let z = head xs
        -- result = z -> path{0} -> ... -> path{n} -> z
        Left $ dropWhile (/= z) visited ++ [a, z]
    Just as -> mapM_ (\x -> ensureDAG' x (visited ++ [a]) g) as

-- これが呼ばれるのはまだrenameされる前
toIdentList :: [Stmt] -> [IdentifierPlus]
toIdentList [] = []
toIdentList ((StmtLet _ mxt _):ds) = mxt : toIdentList ds
toIdentList ((StmtDef xds):ds) = do
  let mxts = map (\(_, (_, mxt, _, _)) -> mxt) xds
  mxts ++ toIdentList ds
toIdentList ((StmtConstDecl _ mxt):ds) = mxt : toIdentList ds
toIdentList ((StmtLetInductive _ _ mxt _):ds) = mxt : toIdentList ds
toIdentList ((StmtLetCoinductive _ _ mxt _):ds) = mxt : toIdentList ds
toIdentList ((StmtLetInductiveIntro _ b _ _ _ _ _ _ _):ss) = b : toIdentList ss
toIdentList ((StmtLetCoinductiveElim _ b _ _ _ _ _ _ _ _ _):ss) =
  b : toIdentList ss

-- toIdentList ((StmtCoinductive {}):_) = undefined
toStmtLetFooter :: Path Abs File -> (Meta, Identifier, WeakTermPlus) -> Stmt
toStmtLetFooter path (m, x, t) = do
  let x' = "(" <> T.pack (toFilePath path) <> ":" <> x <> ")" -- user cannot write this var since it contains parenthesis
  let m' = m {metaIsAppropriateAsCompletionCandidate = False}
  StmtLet m' (m', x', t) (m, WeakTermUpsilon x)

toStmtLetHeader :: Path Abs File -> (Meta, Identifier, WeakTermPlus) -> Stmt
toStmtLetHeader path (m, x, t) = do
  let x' = "(" <> T.pack (toFilePath path) <> ":" <> x <> ")" -- user cannot write this var since it contains parenthesis
  let m' = m {metaIsAppropriateAsCompletionCandidate = False}
  StmtLet m' (m, x, t) (m', WeakTermUpsilon x')
-- reverseLookup :: Eq a => a -> [(a, a)] -> Maybe a
-- reverseLookup
