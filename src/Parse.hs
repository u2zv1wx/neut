{-# LANGUAGE OverloadedStrings #-}

module Parse
  ( parse
  , complete
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.List
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
import Reduce.WeakTerm

parse :: Path Abs File -> WithEnv WeakStmt
parse inputPath = do
  content <- liftIO $ TIO.readFile $ toFilePath inputPath
  stmtList <- strToTree content (toFilePath inputPath) >>= parse'
  stmtList' <- renameQuasiStmtList stmtList
  concatQuasiStmtList stmtList'

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

parse' :: [TreePlus] -> WithEnv [QuasiStmt]
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
  xis <- interpretEnumItem ts
  m' <- adjustPhase m
  insEnumEnv m' name xis
  parse' as
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
              let header = map (toQuasiStmtLetHeader newFilePath) mxs
              defList <- parse' as
              return $ header ++ defList
            Nothing -> do
              content <- liftIO $ TIO.readFile $ toFilePath newFilePath
              modify (\env -> env {currentFilePath = newFilePath})
              modify (\env -> env {phase = 1 + phase env})
              includedQuasiStmtList <- strToTree content path >>= parse'
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
  if name `S.member` cenv
    then throwError' $ "the constant " <> name <> " is already defined"
    else do
      modify (\e -> e {constantEnv = S.insert name (constantEnv e)})
      defList <- parse' as
      m' <- adjustPhase m
      mn' <- adjustPhase mn
      return $ QuasiStmtConstDecl m' (mn', name, t') : defList
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
  stmtList1 <- parseInductive ts
  stmtList2 <- parse' as
  return $ stmtList1 ++ stmtList2
parse' ((m, TreeNode (coind@(_, TreeAtom "coinductive"):name@(mFun, TreeAtom _):xts@(_, TreeNode _):rest)):as) =
  parse' $ (m, TreeNode [coind, (mFun, TreeNode (name : xts : rest))]) : as
parse' ((_, TreeNode ((_, TreeAtom "coinductive"):ts)):as) = do
  stmtList1 <- parseCoinductive ts
  stmtList2 <- parse' as
  return $ stmtList1 ++ stmtList2
parse' ((m, TreeNode [(_, TreeAtom "let"), xt, e]):as) = do
  m' <- adjustPhase m
  e' <- macroExpand e >>= interpret
  (mx, x, t) <- macroExpand xt >>= interpretIdentifierPlus
  defList <- parse' as
  return $ QuasiStmtLet m' (mx, x, t) e' : defList
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
      return $ QuasiStmtLet meta' (meta', name, t) e' : defList

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
insImplicitBegin _ = throwError' "insImplicitBegin"

extractFunName :: TreePlus -> WithEnv Identifier
extractFunName (_, TreeNode ((_, TreeAtom x):_)) = return x
extractFunName (_, TreeNode ((_, TreeNode [(_, TreeAtom x), _]):_)) = return x
extractFunName _ = throwError' "extractFunName"

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

concatQuasiStmtList :: [QuasiStmt] -> WithEnv WeakStmt
concatQuasiStmtList [] = do
  return $ WeakStmtReturn (emptyMeta, WeakTermEnumIntro $ EnumValueLabel "unit")
-- for test
concatQuasiStmtList [QuasiStmtLet _ _ e] = do
  return $ WeakStmtReturn e
concatQuasiStmtList (QuasiStmtConstDecl m xt:es) = do
  cont <- concatQuasiStmtList es
  return $ WeakStmtConstDecl m xt cont
concatQuasiStmtList (QuasiStmtLet m xt e:es) = do
  cont <- concatQuasiStmtList es
  return $ WeakStmtLet m xt e cont
concatQuasiStmtList (QuasiStmtLetWT m xt e:es) = do
  cont <- concatQuasiStmtList es
  return $ WeakStmtLetWT m xt e cont
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
concatQuasiStmtList (QuasiStmtLetInductiveIntro m bt xts yts ats bts bInner isub as:ss) = do
  yts' <- mapM (internalize isub (ats ++ bts)) yts
  -- let s =
  --       QuasiStmtLet
  --         m
  --         bt
  --         ( m
  --         , WeakTermPiIntro
  --             (xts ++ yts)
  --             ( m
  --             , WeakTermPiIntro
  --                 (ats ++ bts) -- ats = [list : (...)], bts = [nil : Pi (yts). list A, cons : (...)]
  --                 (m, WeakTermPiElim bInner yts')))
  insInductive as bt -- register the constructor (if necessary)
  cont <- concatQuasiStmtList ss
  return $
    WeakStmtLetWT
      m
      bt
      ( m
      , WeakTermPiIntro
          (xts ++ yts)
          ( m
          , WeakTermPiIntro
              (ats ++ bts) -- ats = [list : (...)], bts = [nil : Pi (yts). list A, cons : (...)]
              (m, WeakTermPiElim bInner yts')))
      cont
  -- concatQuasiStmtList $ s : ss
concatQuasiStmtList (QuasiStmtLetCoinductiveElim m bt xtsyt codInner ats bts yt e1 e2 csub asOuter:ss) = do
  e2' <- reduceWeakTermPlus <$> externalize csub (ats ++ bts) codInner e2
  -- let s =
  --       QuasiStmtLet
  --         m
  --         bt
  --         ( m
  --         , WeakTermPiIntro
  --             xtsyt
  --             (m, WeakTermSigmaElim codOuter (ats ++ bts ++ [yt]) e1 e2'))
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
  -- concatQuasiStmtList $ s : ss

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

newHole :: WithEnv WeakTermPlus
newHole = do
  h <- newNameWith "hole-parse-zeta"
  return (emptyMeta, WeakTermZeta h)

checkKeywordSanity :: Identifier -> WithEnv ()
checkKeywordSanity "" = throwError' "empty string for a keyword"
checkKeywordSanity x
  | T.last x == '+' = throwError' "A +-suffixed name cannot be a keyword"
checkKeywordSanity _ = return ()

insEnumEnv :: Meta -> Identifier -> [(Identifier, Int)] -> WithEnv ()
insEnumEnv m name xis = do
  eenv <- gets enumEnv
  let definedEnums = Map.keys eenv ++ map fst (concat (Map.elems eenv))
  case find (`elem` definedEnums) $ name : map fst xis of
    Just x ->
      throwError' $
      T.pack (showMeta m) <>
      ": " <> "the constant `" <> x <> "` is already defined"
    _ -> do
      let (xs, is) = unzip xis
      let rev = Map.fromList $ zip xs (zip (repeat name) is)
      modify
        (\e ->
           e
             { enumEnv = Map.insert name xis (enumEnv e)
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
toIdentList :: [QuasiStmt] -> [IdentifierPlus]
toIdentList [] = []
toIdentList ((QuasiStmtLet _ mxt _):ds) = mxt : toIdentList ds
toIdentList ((QuasiStmtDef xds):ds) = do
  let mxts = map (\(_, (_, mxt, _, _)) -> mxt) xds
  mxts ++ toIdentList ds
toIdentList ((QuasiStmtConstDecl _ mxt):ds) = mxt : toIdentList ds
toIdentList ((QuasiStmtLetInductive _ _ mxt _):ds) = mxt : toIdentList ds
toIdentList ((QuasiStmtLetCoinductive _ _ mxt _):ds) = mxt : toIdentList ds
toIdentList ((QuasiStmtLetInductiveIntro _ b _ _ _ _ _ _ _):ss) =
  b : toIdentList ss
toIdentList ((QuasiStmtLetCoinductiveElim _ b _ _ _ _ _ _ _ _ _):ss) =
  b : toIdentList ss

toQuasiStmtLetFooter ::
     Path Abs File -> (Meta, Identifier, WeakTermPlus) -> QuasiStmt
toQuasiStmtLetFooter path (m, x, t) = do
  let x' = "(" <> T.pack (toFilePath path) <> ":" <> x <> ")" -- user cannot write this var since it contains parenthesis
  let m' = m {metaIsAppropriateAsCompletionCandidate = False}
  QuasiStmtLet m' (m', x', t) (m, WeakTermUpsilon x)

toQuasiStmtLetHeader ::
     Path Abs File -> (Meta, Identifier, WeakTermPlus) -> QuasiStmt
toQuasiStmtLetHeader path (m, x, t) = do
  let x' = "(" <> T.pack (toFilePath path) <> ":" <> x <> ")" -- user cannot write this var since it contains parenthesis
  let m' = m {metaIsAppropriateAsCompletionCandidate = False}
  QuasiStmtLet m' (m, x, t) (m', WeakTermUpsilon x')
