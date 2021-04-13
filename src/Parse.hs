module Parse
  ( parse,
  )
where

import Control.Monad
import Data.Basic
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.IORef
import Data.List (find)
import Data.Log
import Data.Namespace
import qualified Data.Text as T
import Data.Tree
import Data.WeakTerm
import Parse.Discern
import Parse.Interpret
import Text.Read (readMaybe)

parse :: [TreePlus] -> IO [WeakStmt]
parse stmtTreeList =
  case stmtTreeList of
    [] ->
      return []
    headStmt : restStmtList -> do
      case headStmt of
        (m, TreeNode ((_, TreeLeaf headAtom) : rest)) ->
          case headAtom of
            --
            -- basic statements
            --
            "define"
              | [xt, e] <- rest -> do
                def <- parseDef True m xt e
                defList <- parse restStmtList
                return $ def : defList
              | otherwise ->
                raiseSyntaxError m "(define TREE TREE)"
            "define-opaque"
              | [xt, e] <- rest -> do
                def <- parseDef False m xt e
                defList <- parse restStmtList
                return $ def : defList
              | otherwise ->
                raiseSyntaxError m "(define-opaque TREE TREE)"
            "reduce"
              | [e] <- rest -> do
                e' <- interpret e >>= discern
                defList <- parse restStmtList
                t <- newAster m
                return $ WeakStmtDef m Nothing t e' : defList
              | otherwise ->
                raiseSyntaxError m "(reduce TREE)"
            "define-enum"
              | (_, TreeLeaf name) : ts <- rest -> do
                name' <- withSectionPrefix name
                xis <- interpretEnumItem m name' ts
                insEnumEnv m name' xis
                parse restStmtList
              | otherwise ->
                raiseSyntaxError m "(define-enum LEAF TREE ... TREE)"
            --
            -- namespace-related statements
            --
            "section"
              | [(_, TreeLeaf s)] <- rest ->
                handleSection s (parse restStmtList)
              | otherwise ->
                raiseSyntaxError m "(section LEAF)"
            "end"
              | [(_, TreeLeaf s)] <- rest -> do
                handleEnd m s (parse restStmtList)
              | otherwise ->
                raiseSyntaxError m "(end LEAF)"
            "define-prefix"
              | [(_, TreeLeaf from), (_, TreeLeaf to)] <- rest -> do
                modifyIORef' nsEnv $ \env -> (from, to) : env
                parse restStmtList
              | otherwise ->
                raiseSyntaxError m "(define-prefix LEAF LEAF)"
            "remove-prefix"
              | [(_, TreeLeaf from), (_, TreeLeaf to)] <- rest -> do
                modifyIORef' nsEnv $ \env -> filter (/= (from, to)) env
                parse restStmtList
              | otherwise ->
                raiseSyntaxError m "(remove-prefix LEAF LEAF)"
            "use"
              | [(_, TreeLeaf s)] <- rest ->
                use s >> parse restStmtList
              | otherwise ->
                raiseSyntaxError m "(use LEAF)"
            "unuse"
              | [(_, TreeLeaf s)] <- rest ->
                unuse s >> parse restStmtList
              | otherwise ->
                raiseSyntaxError m "(unuse LEAF)"
            --
            -- other statements
            --
            "set-as-data"
              | ((_, TreeLeaf name) : (_, TreeLeaf intStr) : constructorNameList) <- rest,
                Just i <- readMaybe (T.unpack intStr) -> do
                xs <- mapM (extractLeaf >=> withSectionPrefix) constructorNameList
                name' <- withSectionPrefix name
                modifyIORef' dataEnv $ \env -> Map.insert name' xs env
                forM_ (zip xs [0 ..]) $ \(x, k) -> modifyIORef' constructorEnv $ \env -> Map.insert x (i, k) env
                parse restStmtList
              | otherwise -> do
                raiseSyntaxError m "(set-as-data LEAF INT LEAF*)"
            "statement" ->
              parse $ rest ++ restStmtList
            _ ->
              interpretAux headStmt restStmtList
        _ ->
          interpretAux headStmt restStmtList

interpretAux :: TreePlus -> [TreePlus] -> IO [WeakStmt]
interpretAux headStmt restStmtList = do
  e <- interpret headStmt >>= discern
  let m = metaOf e
  t <- newAster m
  defList <- parse restStmtList
  return $ WeakStmtDef m Nothing t e : defList

parseDef :: Bool -> Hint -> TreePlus -> TreePlus -> IO WeakStmt
parseDef isReducible m xt e = do
  e' <- interpret e >>= discern
  (_, x, t) <- prefixTextPlus xt >>= interpretIdentPlus >>= discernIdentPlus
  return $ WeakStmtDef m (Just (isReducible, x)) t e'

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

extractLeaf :: TreePlus -> IO T.Text
extractLeaf t =
  case t of
    (_, TreeLeaf x) ->
      return x
    _ ->
      raiseSyntaxError (fst t) "LEAF"
