{-# LANGUAGE OverloadedStrings #-}

module Parse
  ( parse
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

-- data Stmt
--   = StmtLet
--       Meta
--       IdentifierPlus -- the `(x : t)` in `let (x : t) = e`
--       WeakTermPlus -- the `e` in `let x = e`
--   | StmtConstDecl IdentifierPlus
-- {} parse {the output term is correctly renamed}
-- (The postcondition is guaranteed by the assertion of `rename`.)
parse :: T.Text -> Path Abs File -> WithEnv WeakTermPlus
parse s inputPath
  -- i <- newCount
  -- modify (\env -> env {fileEnv = Map.insert inputPath (i, []) (fileEnv env)})
 = do
  stmtList <- strToTree s (toFilePath inputPath) >>= parse'
  stmtList' <- renameStmtList stmtList
  concatStmtList stmtList'
  -- e <- strToTree s (toFilePath inputPath) >>= parse' >>= concatStmtList
  -- -- p' e
  -- rename e
  -- strToTree s inputPath >>= parse' >>= concatStmtList >>= rename

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
  insEnumEnv m name indexList
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
  let ascription = StmtConstDecl (constName, isEnumType)
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
parse' ((_, TreeNode [(_, TreeAtom "constant"), (_, TreeAtom name), t]):as) = do
  t' <- macroExpand t >>= interpret
  cenv <- gets constantEnv
  if name `S.member` cenv
    then throwError' $ "the constant " <> name <> " is already defined"
    else do
      modify (\e -> e {constantEnv = S.insert name (constantEnv e)})
      defList <- parse' as
      return $ StmtConstDecl (name, t') : defList
parse' ((m, TreeNode [(mDef, TreeAtom "definition"), name@(_, TreeAtom _), body]):as) =
  parse' $ (m, TreeNode [(mDef, TreeAtom "let"), name, body]) : as
parse' ((m, TreeNode (def@(_, TreeAtom "definition"):name@(mFun, TreeAtom _):xts@(_, TreeNode _):body:rest)):as) =
  parse' $ (m, TreeNode [def, (mFun, TreeNode (name : xts : body : rest))]) : as
parse' ((_, TreeNode ((_, TreeAtom "definition"):xds)):as) = do
  stmt <- parseDef xds
  stmtList <- parse' as
  return $ stmt : stmtList
parse' ((m, TreeNode [(_, TreeAtom "let"), xt, e]):as) = do
  e' <- macroExpand e >>= interpret
  (x, t) <- macroExpand xt >>= interpretIdentifierPlus
  defList <- parse' as
  return $ StmtLet m (x, t) e' : defList
parse' (a:as) = do
  e <- macroExpand a
  if isSpecialForm e
    then parse' $ e : as
    else do
      e'@(meta, _) <- interpret e
      name <- newNameWith "hole-parse-last"
      t <- newHole
      defList <- parse' as
      return $ StmtLet meta (name, t) e' : defList

parseDef :: [TreePlus] -> WithEnv Stmt
parseDef xds = do
  xds' <- mapM (insImplicitBegin >=> macroExpand) xds
  xs <- mapM extractFunName xds'
  xds'' <- mapM interpretIter xds'
  return $ StmtDef $ zip xs xds''

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
isSpecialForm (_, TreeNode [(_, TreeAtom "definition"), _, _]) = True
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
concatStmtList (StmtConstDecl xt:es) = do
  cont <- concatStmtList es
  return (emptyMeta, WeakTermConstDecl xt cont)
concatStmtList (StmtLet m xt e:es) = do
  cont <- concatStmtList es
  return (m, WeakTermPiElim (emptyMeta, WeakTermPiIntro [xt] cont) [e])
concatStmtList (StmtDef xds:ss) = do
  let ds = map snd xds
  let baseSub = map defToSub ds
  let nTimes = length baseSub
  let sub = selfCompose nTimes baseSub
  let varList = map (\(m, (x, _), _, _) -> (m, WeakTermUpsilon x)) ds
  let iterList = map (substWeakTermPlus sub) varList
  -- StmtLetに帰着
  let letList = toLetList $ zip xds iterList
  -- when (length xds >= 2) $ do
  --   p "baseSub:"
  --   p' baseSub
  --   p "letList:"
  --   p' letList
  concatStmtList $ letList ++ ss

toLetList :: [(IdentDef, WeakTermPlus)] -> [Stmt]
toLetList [] = []
toLetList (((x, (m, (_, t), _, _)), iter):rest) =
  StmtLet m (x, t) iter : toLetList rest

defToSub :: Def -> (Identifier, WeakTermPlus)
defToSub (m, (x, t), xts, e) = (x, (m, WeakTermIter (x, t) xts e))

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
toIdentList :: [Stmt] -> [(Meta, Identifier, WeakTermPlus)]
toIdentList [] = []
toIdentList ((StmtLet m (x, t) _):ds) = (m, x, t) : toIdentList ds
toIdentList ((StmtDef xds):ds) = do
  let mxts = map (\(_, (m, (x, t), _, _)) -> (m, x, t)) xds
  mxts ++ toIdentList ds
toIdentList ((StmtConstDecl (x, t)):ds) = (emptyMeta, x, t) : toIdentList ds

toStmtLetFooter :: Path Abs File -> (Meta, Identifier, WeakTermPlus) -> Stmt
toStmtLetFooter path (m, x, t) = do
  let x' = "(" <> T.pack (toFilePath path) <> ":" <> x <> ")" -- user cannot write this var since it contains parenthesis
  StmtLet m (x', t) (m, WeakTermUpsilon x)

toStmtLetHeader :: Path Abs File -> (Meta, Identifier, WeakTermPlus) -> Stmt
toStmtLetHeader path (m, x, t) = do
  let x' = "(" <> T.pack (toFilePath path) <> ":" <> x <> ")" -- user cannot write this var since it contains parenthesis
  StmtLet m (x, t) (m, WeakTermUpsilon x')
