module Parse
  ( parse
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.List
import Path
import Path.IO
import Text.Read (readMaybe)

import qualified Data.HashMap.Strict as Map
import qualified Data.Set as S
import qualified Text.Show.Pretty as Pr

import Data.Basic
import Data.Env
import Data.Tree
import Data.WeakTerm
import Parse.Interpret
import Parse.MacroExpand
import Parse.Read
import Parse.Rename

data Def
  = DefLet
      Meta
      IdentifierPlus -- the `(x : t)` in `let (x : t) = e`
      WeakTermPlus -- the `e` in `let x = e`
  | DefConstDecl IdentifierPlus

-- {} parse {the output term is correctly renamed}
-- (The postcondition is guaranteed by the assertion of `rename`.)
parse :: String -> String -> WithEnv WeakTermPlus
parse s inputPath = do
  strToTree s inputPath >>= parse' >>= concatDefList >>= rename

-- {} parse' {}
-- Parse the head element of the input list.
parse' :: [TreePlus] -> WithEnv [Def]
parse' [] = return []
parse' ((_, TreeNode [(_, TreeAtom "notation"), from, to]):as) = do
  checkNotationSanity from
  modify (\e -> e {notationEnv = notationEnv e ++ [(from, to)]})
  parse' as
parse' ((_, TreeNode [(_, TreeAtom "keyword"), (_, TreeAtom s)]):as) = do
  checkKeywordSanity s
  modify (\e -> e {keywordEnv = S.insert s (keywordEnv e)})
  parse' as
parse' ((_, TreeNode ((_, TreeAtom "enum"):(_, TreeAtom name):ts)):as) = do
  indexList <- mapM extractIdentifier ts
  insEnumEnv name indexList
  -- `constName` is a proof term that `name` is indeed an enum:
  --   enum.choice : is-enum choice
  -- example usage:
  --   print: Pi (A : Univ, prf : is-enum A, str : u8-array A). IO top
  -- This proof term is translated into the number of the contents of the corresponding enum type.
  -- Thus, `enum.choice` is, for example, translated into 2, assuming that choice = {left, right}.
  -- In the example of `print`, this integer in turn represents the length of the array `str`,
  -- which is indispensable for the system call `write`.
  let constName = "enum." ++ name
  modify (\e -> e {constantEnv = S.insert constName (constantEnv e)})
  -- type constraint for constName
  -- e.g. t == is-enum @ (choice)
  isEnumType <- toIsEnumType name
  -- add `(constant enum.choice (is-enum choice))` to defList in order to insert appropriate type constraint
  let ascription = DefConstDecl (constName, isEnumType)
  -- register the name of the constant
  modify (\env -> env {nameEnv = Map.insert constName constName (nameEnv env)})
  defList <- parse' as
  return $ ascription : defList
parse' ((_, TreeNode [(_, TreeAtom "include"), (_, TreeAtom pathString)]):as) =
  case readMaybe pathString :: Maybe String of
    Nothing -> throwError "the argument of `include` must be a string"
    Just path -> do
      oldFilePath <- gets currentFilePath
      newFilePath <- resolveFile (parent oldFilePath) path
      b <- doesFileExist newFilePath
      if not b
        then throwError $ "no such file: " ++ toFilePath newFilePath
        else do
          insertPathInfo oldFilePath newFilePath
          ensureDAG
          denv <- gets defEnv
          case Map.lookup newFilePath denv of
            Just mxs -> do
              let header = map (toDefLetHeader newFilePath) mxs
              defList <- parse' as
              return $ header ++ defList
            Nothing -> do
              content <- liftIO $ readFile $ toFilePath newFilePath
              modify (\e -> e {currentFilePath = newFilePath})
              includedDefList <- strToTree content path >>= parse'
              let mxs = toIdentList includedDefList
              modify (\e -> e {currentFilePath = oldFilePath})
              modify (\env -> env {defEnv = Map.insert newFilePath mxs denv})
              defList <- parse' as
              let footer = map (toDefLetFooter newFilePath) mxs
              let header = map (toDefLetHeader newFilePath) mxs
              return $ includedDefList ++ footer ++ header ++ defList
parse' ((_, TreeNode ((_, TreeAtom "statement"):as1)):as2) = do
  defList1 <- parse' as1
  defList2 <- parse' as2
  return $ defList1 ++ defList2
parse' ((_, TreeNode [(_, TreeAtom "constant"), (_, TreeAtom name), t]):as) = do
  t' <- macroExpand t >>= interpret
  cenv <- gets constantEnv
  if name `S.member` cenv
    then throwError $ "the constant " ++ name ++ " is already defined"
    else do
      modify (\e -> e {constantEnv = S.insert name (constantEnv e)})
      defList <- parse' as
      return $ DefConstDecl (name, t') : defList
parse' ((m, TreeNode [(_, TreeAtom "let"), xt, e]):as) = do
  e' <- macroExpand e >>= interpret
  (x, t) <- macroExpand xt >>= interpretIdentifierPlus
  defList <- parse' as
  return $ DefLet m (x, t) e' : defList
parse' (a:as) = do
  e <- macroExpand a
  if isSpecialForm e
    then parse' $ e : as
    else do
      e'@(meta, _) <- interpret e
      name <- newNameWith "hole-parse-last"
      t <- newHole
      defList <- parse' as
      return $ DefLet meta (name, t) e' : defList

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
isSpecialForm _ = False

-- {} toIsEnumType {}
toIsEnumType :: Identifier -> WithEnv WeakTermPlus
toIsEnumType name = do
  return
    ( emptyMeta
    , WeakTermPiElim
        (emptyMeta, WeakTermConst "is-enum")
        [(emptyMeta, WeakTermEnum $ EnumTypeLabel name)])

-- {} concatDefList {}
-- Represent the list of Defs in the target language, using `let`.
-- (Note that `let x := e1 in e2` can be represented as `(lam x e2) e1`.)
concatDefList :: [Def] -> WithEnv WeakTermPlus
concatDefList [] = do
  return (emptyMeta, WeakTermEnumIntro $ EnumValueLabel "unit")
-- for test
concatDefList [DefLet _ _ e] = do
  return e
concatDefList (DefConstDecl xt:es) = do
  cont <- concatDefList es
  return (emptyMeta, WeakTermConstDecl xt cont)
concatDefList (DefLet m xt e:es) = do
  cont <- concatDefList es
  return (m, WeakTermPiElim (emptyMeta, WeakTermPiIntro [xt] cont) [e])

-- {} newHole {}
newHole :: WithEnv WeakTermPlus
newHole = do
  h <- newNameWith "hole-parse-zeta"
  return (emptyMeta, WeakTermZeta h)

-- {} checkKeywordSanity {}
checkKeywordSanity :: Identifier -> WithEnv ()
checkKeywordSanity "" = throwError "empty string for a keyword"
checkKeywordSanity x
  | last x == '+' = throwError "A +-suffixed name cannot be a keyword"
checkKeywordSanity _ = return ()

-- {} insEnumEnv {}
insEnumEnv :: Identifier -> [Identifier] -> WithEnv ()
insEnumEnv name enumList = do
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
      throwError $ "found cyclic inclusion:\n" ++ Pr.ppShow cyclicPath

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

toIdentList :: [Def] -> [(Meta, Identifier, WeakTermPlus)]
toIdentList [] = []
toIdentList ((DefLet m (x, t) _):ds) = (m, x, t) : toIdentList ds
toIdentList ((DefConstDecl (x, t)):ds) = (emptyMeta, x, t) : toIdentList ds

toDefLetFooter :: Path Abs File -> (Meta, Identifier, WeakTermPlus) -> Def
toDefLetFooter path (m, x, t) = do
  let x' = "(" ++ toFilePath path ++ ":" ++ x ++ ")" -- user cannot write this var since it contains parenthesis
  DefLet m (x', t) (m, WeakTermUpsilon x)

toDefLetHeader :: Path Abs File -> (Meta, Identifier, WeakTermPlus) -> Def
toDefLetHeader path (m, x, t) = do
  let x' = "(" ++ toFilePath path ++ ":" ++ x ++ ")"
  DefLet m (x, t) (m, WeakTermUpsilon x')
