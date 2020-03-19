{-# LANGUAGE OverloadedStrings #-}

module Parse
  ( parse
  , complete
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.List
import Data.Maybe (catMaybes)
import Data.Monoid ((<>))
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
import Parse.Rule
import Parse.Utility

parse :: Path Abs File -> WithEnv WeakStmt
parse inputPath = do
  content <- liftIO $ TIO.readFile $ toFilePath inputPath
  stmtList <- strToTree content inputPath >>= parse'
  stmtList' <- renameQuasiStmtList stmtList
  concatQuasiStmtList stmtList'

complete :: Path Abs File -> Line -> Column -> WithEnv [String]
complete inputPath l c = do
  info <- parseForCompletion inputPath l c
  return $ showCompInfo info

showCompInfo :: CompInfo -> [String]
showCompInfo [] = []
showCompInfo ((x, m):xms) = do
  case getPosInfo m of
    Nothing -> showCompInfo xms
    Just (path, (_, l, c)) -> do
      let pathStr = "\"" <> toFilePath path <> "\""
      let x' = T.unpack $ asText x
      let str =
            "(\"" ++
            x' ++ "\" (" ++ pathStr ++ " " ++ show l ++ " " ++ show c ++ "))"
      str : showCompInfo xms

parseForCompletion :: Path Abs File -> Line -> Column -> WithEnv CompInfo
parseForCompletion inputPath l c = do
  content <- liftIO $ TIO.readFile $ toFilePath inputPath
  s <- newNameWith' "cursor"
  case modifyFileForCompletion s content l c of
    Nothing -> return []
    Just (prefix, content') -> do
      stmtList <- strToTree content' inputPath >>= parse'
      case compInfo s stmtList of
        Right () -> return []
        Left info -> do
          let info' = filter (filterCompInfo prefix) info
          let compareLoc m1 m2 = metaLocation m2 `compare` metaLocation m1
          return $ nub $ sortBy (\(_, m1) (_, m2) -> compareLoc m1 m2) info'

-- 必要ならここでprefixの情報も与える
-- parenとかのときは何も返さないからNothingにする
modifyFileForCompletion ::
     CursorName -> T.Text -> Line -> Column -> Maybe (Prefix, T.Text)
modifyFileForCompletion (I (s, _)) content l c = do
  let xs = T.lines content
  let (ys, ws) = splitAt (l - 1) xs
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

parse' :: [TreePlus] -> WithEnv [QuasiStmt]
parse' [] = return []
parse' ((_, TreeNode [(_, TreeAtom "notation"), from, to]):as) = do
  checkNotationSanity from
  modify (\e -> e {notationEnv = (from, to) : notationEnv e})
  parse' as
parse' ((m, TreeNode [(_, TreeAtom "keyword"), (_, TreeAtom s)]):as) = do
  checkKeywordSanity m s
  modify (\e -> e {keywordEnv = S.insert s (keywordEnv e)})
  parse' as
parse' ((m, TreeNode ((_, TreeAtom "enum"):(_, TreeAtom name):ts)):as) = do
  xis <- interpretEnumItem m ts
  m' <- adjustPhase m
  insEnumEnv m' name xis
  parse' as
parse' ((m, TreeNode [(_, TreeAtom "include"), (_, TreeAtom pathString)]):as) =
  case readMaybe (T.unpack pathString) :: Maybe String of
    Nothing -> raiseError m "the argument of `include` must be a string"
    Just path -> do
      oldFilePath <- gets currentFilePath
      newFilePath <- resolveFile (parent oldFilePath) path
      b <- doesFileExist newFilePath
      if not b
        then raiseError m $ "no such file: " <> T.pack (toFilePath newFilePath)
        else do
          insertPathInfo oldFilePath newFilePath
          ensureDAG m
          denv <- gets fileEnv
          case Map.lookup newFilePath denv of
            Just mxs -> do
              let header = map (toQuasiStmtLetHeader newFilePath) mxs
              defList <- parse' as
              return $ header ++ defList
            Nothing -> do
              content <- liftIO $ TIO.readFile $ toFilePath newFilePath
              modify (\env -> env {currentFilePath = newFilePath})
              modify (\env -> env {phase = 1 + phase env})
              includedQuasiStmtList <- strToTree content newFilePath >>= parse'
              -- includedQuasiStmtList <- strToTree content path >>= parse'
              let mxs = toIdentList includedQuasiStmtList
              modify (\env -> env {currentFilePath = oldFilePath})
              modify (\env -> env {phase = 1 + phase env})
              modify (\env -> env {fileEnv = Map.insert newFilePath mxs denv})
              defList <- parse' as
              let footer = map (toQuasiStmtLetFooter newFilePath) mxs
              let header = map (toQuasiStmtLetHeader newFilePath) mxs
              return $ includedQuasiStmtList ++ footer ++ header ++ defList
parse' ((_, TreeNode ((_, TreeAtom "statement"):as1)):as2) = do
  defList1 <- parse' as1
  defList2 <- parse' as2
  return $ defList1 ++ defList2
parse' ((m, TreeNode [(_, TreeAtom "constant"), (mn, TreeAtom name), t]):as) = do
  t' <- macroExpand t >>= interpret
  cenv <- gets constantEnv
  case Map.lookup name cenv of
    Just _ -> raiseError m $ "the constant " <> name <> " is already defined"
    Nothing -> do
      i <- newCount
      modify (\e -> e {constantEnv = Map.insert name i (constantEnv e)})
      defList <- parse' as
      m' <- adjustPhase m
      mn' <- adjustPhase mn
      return $ QuasiStmtConstDecl m' (mn', I (name, i), t') : defList
parse' ((_, TreeNode ((_, TreeAtom "attribute"):(_, TreeAtom name):attrList)):as) = do
  ss1 <- mapM (parseAttr name) attrList
  ss2 <- parse' as
  return $ ss1 ++ ss2
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
parse' ((m, TreeNode ((_, TreeAtom "inductive"):ts)):as) = do
  stmtList1 <- parseInductive m ts
  stmtList2 <- parse' as
  return $ stmtList1 ++ stmtList2
parse' ((m, TreeNode (coind@(_, TreeAtom "coinductive"):name@(mFun, TreeAtom _):xts@(_, TreeNode _):rest)):as) =
  parse' $ (m, TreeNode [coind, (mFun, TreeNode (name : xts : rest))]) : as
parse' ((m, TreeNode ((_, TreeAtom "coinductive"):ts)):as) = do
  stmtList1 <- parseCoinductive m ts
  stmtList2 <- parse' as
  return $ stmtList1 ++ stmtList2
parse' ((m, TreeNode [(mLet, TreeAtom "let"), (mx, TreeAtom x), t, e]):as) = do
  let xt = (mx, TreeNode [(mx, TreeAtom x), t])
  parse' ((m, TreeNode [(mLet, TreeAtom "let"), xt, e]) : as)
parse' ((m, TreeNode [(_, TreeAtom "let"), xt, e]):as) = do
  m' <- adjustPhase m
  e' <- macroExpand e >>= interpret
  (mx, x, t) <- macroExpand xt >>= interpretIdentifierPlus
  defList <- parse' as
  case e' of
    (_, WeakTermPiElim f args)
      | (mmxs, args') <- unzip $ map parseBorrow args
      , mxs <- catMaybes mmxs
      , not (null mxs) -> do
        xts <- mapM toIdentPlus mxs
        let app = (m, WeakTermPiElim f args')
        return $ QuasiStmtLetSigma m (xts ++ [(mx, x, t)]) app : defList
    _ -> return $ QuasiStmtLet m' (mx, x, t) e' : defList
parse' (a:as) = do
  e <- macroExpand a
  if isSpecialForm e
    then parse' $ e : as
    else do
      e' <- interpret e
      case e' of
        (m, WeakTermPiElim f args)
          | (mmxs, args') <- unzip $ map parseBorrow args
          , mxs <- catMaybes mmxs
          , not (null mxs) -> do
            tmp <- newNameWith'' "borrow"
            xts <- mapM toIdentPlus $ mxs ++ [(m, tmp)]
            let app = (m, WeakTermPiElim f args')
            defList <- parse' as
            return $ QuasiStmtLetSigma m xts app : defList
        (m, _) -> do
          name <- newNameWith'' "hole-parse-last"
          t <- newHole m
          defList <- parse' as
          let m' = m {metaIsAppropriateAsCompletionCandidate = False}
          return $ QuasiStmtLet m' (m', name, t) e' : defList

parseBorrow :: WeakTermPlus -> (Maybe (Meta, Identifier), WeakTermPlus)
parseBorrow (m, WeakTermUpsilon (I (s, _)))
  | T.length s > 1
  , T.head s == '&' =
    (Just (m, asIdent $ T.tail s), (m, WeakTermUpsilon $ asIdent $ T.tail s))
parseBorrow t = (Nothing, t)

parseAttr :: T.Text -> TreePlus -> WithEnv QuasiStmt
parseAttr name (m, TreeNode [(_, TreeAtom "implicit"), (_, TreeAtom num)]) = do
  case readMaybe $ T.unpack num of
    Nothing -> undefined
    Just i -> return $ QuasiStmtImplicit m (asIdent name) i
parseAttr _ t = raiseError (fst t) $ "invalid attribute: " <> showAsSExp t

parseDef :: [TreePlus] -> WithEnv QuasiStmt
parseDef xds = do
  xds' <- mapM (insImplicitBegin >=> macroExpand) xds
  mxs <- mapM extractFunName xds'
  xds'' <- mapM interpretIter xds'
  return $ QuasiStmtDef $ zip mxs xds''

insImplicitBegin :: TreePlus -> WithEnv TreePlus
insImplicitBegin (m, TreeNode (xt:xts:body:rest)) = do
  let m' = fst body
  let beginBlock = (m', TreeNode ((m', TreeAtom "begin") : body : rest))
  return (m, TreeNode [xt, xts, beginBlock])
insImplicitBegin t = raiseSyntaxError t "(TREE TREE TREE ...)"

extractFunName :: TreePlus -> WithEnv Identifier
extractFunName (_, TreeNode ((_, TreeAtom x):_)) = return $ asIdent x
extractFunName (_, TreeNode ((_, TreeNode [(_, TreeAtom x), _]):_)) =
  return $ asIdent x
extractFunName t = raiseSyntaxError t "(LEAF ...) | ((LEAF TREE) ...)"

isSpecialForm :: TreePlus -> Bool
isSpecialForm (_, TreeNode [(_, TreeAtom "notation"), _, _]) = True
isSpecialForm (_, TreeNode [(_, TreeAtom "keyword"), (_, TreeAtom _)]) = True
isSpecialForm (_, TreeNode ((_, TreeAtom "enum"):(_, TreeAtom _):_)) = True
isSpecialForm (_, TreeNode [(_, TreeAtom "include"), (_, TreeAtom _)]) = True
isSpecialForm (_, TreeNode ((_, TreeAtom "attribute"):_)) = True
isSpecialForm (_, TreeNode [(_, TreeAtom "constant"), (_, TreeAtom _), _]) =
  True
isSpecialForm (_, TreeNode ((_, TreeAtom "statement"):_)) = True
isSpecialForm (_, TreeNode [(_, TreeAtom "let"), _, _]) = True
isSpecialForm (_, TreeNode ((_, TreeAtom "definition"):_)) = True
isSpecialForm (_, TreeNode ((_, TreeAtom "inductive"):_)) = True
isSpecialForm (_, TreeNode ((_, TreeAtom "coinductive"):_)) = True
isSpecialForm _ = False

-- funAndArgs :: TreePlus -> Maybe (TreePlus, [TreePlus])
-- funAndArgs (m, TreeNode (f : args))
--   | (_, TreeAtom "upsilon") <- f = Nothing
--   | (_, TreeAtom "pi") <- f = Nothing
--   | (_, TreeAtom "pi-introduction") <- f = Nothing
--   | (_, TreeAtom "pi-elimination") <- f = Nothing
--   | (_, TreeAtom "sigma") <- f = Nothing
--   | (_, TreeAtom "sigma-introduction") <- f = Nothing
--   | (_, TreeAtom "sigma-elimination") <- f = Nothing
--   | (_, TreeAtom "iterate") <- f = Nothing
--   | (_, TreeAtom "zeta") <- f = Nothing
--   | (_, TreeAtom "constant") <- f = Nothing
--   | (_, TreeAtom "f16") <- f = Nothing
--   | (_, TreeAtom "f32") <- f = Nothing
--   | (_, TreeAtom "f64") <- f = Nothing
--   | (_, TreeAtom "enum") <- f = Nothing
--   | (_, TreeAtom "enum-introduction") <- f = Nothing
--   | (_, TreeAtom "enum-elimination") <- f = Nothing
--   | (_, TreeAtom "array") <- f = Nothing
--   | (_, TreeAtom "array-introduction") <- f = Nothing
--   | (_, TreeAtom "array-elimination") <- f = Nothing
--   | (_, TreeAtom "enum") <- f = Nothing
-- funAndArgs _ = Nothing
concatQuasiStmtList :: [QuasiStmt] -> WithEnv WeakStmt
concatQuasiStmtList [] = do
  return $ WeakStmtReturn (emptyMeta, WeakTermEnumIntro $ EnumValueLabel "unit")
-- -- for test
-- concatQuasiStmtList [QuasiStmtLet _ _ e] = do
--   return $ WeakStmtReturn e
concatQuasiStmtList (QuasiStmtConstDecl m xt:es) = do
  cont <- concatQuasiStmtList es
  return $ WeakStmtConstDecl m xt cont
concatQuasiStmtList (QuasiStmtLet m xt e:es) = do
  cont <- concatQuasiStmtList es
  return $ WeakStmtLet m xt e cont
concatQuasiStmtList (QuasiStmtLetWT m xt e:es) = do
  cont <- concatQuasiStmtList es
  return $ WeakStmtLetWT m xt e cont
concatQuasiStmtList (QuasiStmtLetSigma m xts e:es) = do
  cont <- concatQuasiStmtList es
  return $ WeakStmtLetSigma m xts e cont
concatQuasiStmtList (QuasiStmtImplicit m x i:es) = do
  cont <- concatQuasiStmtList es
  return $ WeakStmtImplicit m x i cont
concatQuasiStmtList (QuasiStmtDef xds:ss) = do
  let ds = map snd xds
  let baseSub = map defToSub ds
  let sub = selfCompose (length baseSub) baseSub
  let varList = map (\(_, (m, x, _), _, _) -> (m, WeakTermUpsilon x)) ds
  let iterList = map (substWeakTermPlus sub) varList
  concatQuasiStmtList $ (toLetList $ zip xds iterList) ++ ss
concatQuasiStmtList ((QuasiStmtLetInductive n m at e):es) = do
  insForm n at e
  cont <- concatQuasiStmtList es
  return $ WeakStmtLetWT m at e cont
concatQuasiStmtList (QuasiStmtLetCoinductive n m at e:es) = do
  insForm n at e
  cont <- concatQuasiStmtList es
  return $ WeakStmtLetWT m at e cont
concatQuasiStmtList (QuasiStmtLetInductiveIntro m (bi, ai) bt xts yts ats bts bInner isub as:ss) = do
  yts' <- mapM (internalize isub (ats ++ bts)) yts
  insInductive as bt -- register the constructor (if necessary)
  cont <- concatQuasiStmtList ss
  return $
    WeakStmtLetInductiveIntro
      m
      (bi, ai)
      bt
      xts
      yts
      (ats ++ bts)
      (m, WeakTermPiElim bInner yts')
      cont
  -- return $
  --   WeakStmtLetWT
  --     m
  --     bt
  --     ( m
  --     , WeakTermPiIntro
  --         (xts ++ yts)
  --         ( m
  --         , WeakTermPiIntroPlus
  --             bi
  --             ai
  --             [] -- index/subst info is supplied after elaboration
  --             []
  --             (ats ++ bts) -- ats = [list : (...)], bts = [nil : Pi (yts). list A, cons : (...)]
  --             (m, WeakTermPiElim bInner yts')))
  --     cont
concatQuasiStmtList (QuasiStmtLetCoinductiveElim m bt xtsyt codInner ats bts yt e1 e2 csub asOuter:ss) = do
  e2' <- externalize csub (ats ++ bts) codInner e2
  insCoinductive asOuter bt -- register the destructor (if necessary)
  cont <- concatQuasiStmtList ss
  let codOuter = substWeakTermPlus csub codInner
  return $
    WeakStmtLetWT
      m
      bt
      ( m
      , WeakTermPiIntro
          xtsyt
          (m, WeakTermSigmaElim codOuter (ats ++ bts ++ [yt]) e1 e2'))
      cont

toLetList :: [(IdentDef, WeakTermPlus)] -> [QuasiStmt]
toLetList [] = []
toLetList (((x, (m, (mx, _, t), _, _)), iter):rest) =
  QuasiStmtLet m (mx, x, t) iter : toLetList rest

defToSub :: Def -> (Identifier, WeakTermPlus)
defToSub (m, (mx, x, t), xts, e) = (x, (m, WeakTermIter (mx, x, t) xts e))

selfCompose :: Int -> SubstWeakTerm -> SubstWeakTerm
selfCompose 0 sub = sub
selfCompose n sub = compose sub $ selfCompose (n - 1) sub

compose :: SubstWeakTerm -> SubstWeakTerm -> SubstWeakTerm
compose s1 s2 = do
  let domS2 = map fst s2
  let codS2 = map snd s2
  let codS2' = map (substWeakTermPlus s1) codS2
  let s1' = filter (\(ident, _) -> ident `notElem` domS2) s1
  s1' ++ zip domS2 codS2'

newHole :: Meta -> WithEnv WeakTermPlus
newHole m = do
  h <- newNameWith'' "hole-parse-zeta"
  return (m, WeakTermZeta h)

checkKeywordSanity :: Meta -> T.Text -> WithEnv ()
checkKeywordSanity m "" = raiseError m "empty string for a keyword"
checkKeywordSanity m x
  | T.last x == '+' = raiseError m "A +-suffixed name cannot be a keyword"
checkKeywordSanity _ _ = return ()

insertPathInfo :: Path Abs File -> Path Abs File -> WithEnv ()
insertPathInfo oldFilePath newFilePath = do
  g <- gets includeGraph
  let g' = Map.insertWith (++) oldFilePath [newFilePath] g
  modify (\env -> env {includeGraph = g'})

ensureDAG :: Meta -> WithEnv ()
ensureDAG m = do
  g <- gets includeGraph
  path <- gets mainFilePath
  case ensureDAG' path [] g of
    Right _ -> return ()
    Left cyclicPath -> do
      raiseError m $
        "found cyclic inclusion:\n" <> T.pack (Pr.ppShow cyclicPath)

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
toIdentList :: [QuasiStmt] -> [IdentifierPlus]
toIdentList [] = []
toIdentList ((QuasiStmtLet _ mxt _):ds) = mxt : toIdentList ds
toIdentList ((QuasiStmtLetWT _ mxt _):ds) = mxt : toIdentList ds
toIdentList ((QuasiStmtLetSigma _ mxts _):ds) = mxts ++ toIdentList ds
toIdentList ((QuasiStmtImplicit {}):ds) = toIdentList ds
toIdentList ((QuasiStmtDef xds):ds) = do
  let mxts = map (\(_, (_, mxt, _, _)) -> mxt) xds
  mxts ++ toIdentList ds
toIdentList ((QuasiStmtConstDecl _ (m, x, t)):ds) = (m, x, t) : toIdentList ds
toIdentList ((QuasiStmtLetInductive _ _ mxt _):ds) = mxt : toIdentList ds
toIdentList ((QuasiStmtLetCoinductive _ _ mxt _):ds) = mxt : toIdentList ds
toIdentList ((QuasiStmtLetInductiveIntro _ _ b _ _ _ _ _ _ _):ss) =
  b : toIdentList ss
toIdentList ((QuasiStmtLetCoinductiveElim _ b _ _ _ _ _ _ _ _ _):ss) =
  b : toIdentList ss

toQuasiStmtLetFooter ::
     Path Abs File -> (Meta, Identifier, WeakTermPlus) -> QuasiStmt
toQuasiStmtLetFooter path (m, x, t) = do
  let s' = "(" <> T.pack (toFilePath path) <> ":" <> asText' x <> ")" -- user cannot write this var since it contains parenthesis
  let m' = m {metaIsAppropriateAsCompletionCandidate = False}
  QuasiStmtLet m' (m', I (llvmString s', 0), t) (m, WeakTermUpsilon x)

toQuasiStmtLetHeader ::
     Path Abs File -> (Meta, Identifier, WeakTermPlus) -> QuasiStmt
toQuasiStmtLetHeader path (m, x, t) = do
  let s' = "(" <> T.pack (toFilePath path) <> ":" <> asText' x <> ")" -- user cannot write this var since it contains parenthesis
  let m' = m {metaIsAppropriateAsCompletionCandidate = False}
  QuasiStmtLet m' (m, x, t) (m', WeakTermUpsilon (I (llvmString s', 0)))
