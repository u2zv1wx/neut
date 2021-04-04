module Parse
  ( parse,
  )
where

import Control.Monad.State.Lazy hiding (get)
import Data.Basic
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.List (find)
import Data.Log
import Data.Namespace
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Tree
import Data.WeakTerm
import Parse.Discern
import Parse.Interpret
import Text.Read (readMaybe)

parse :: [TreePlus] -> WithEnv [WeakStmt]
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
                e' <- interpret e >>= discern
                xt' <- prefixTextPlus xt >>= interpretIdentPlus >>= discernIdentPlus
                defList <- parse restStmtList
                return $ WeakStmtDef m xt' e' : defList
              | otherwise ->
                raiseSyntaxError m "(define LEAF TREE TREE) | (define TREE TREE)"
            "declare-enum"
              | (_, TreeLeaf name) : ts <- rest -> do
                name' <- withSectionPrefix name
                xis <- interpretEnumItem m name' ts
                insEnumEnv m name' xis
                parse restStmtList
              | otherwise ->
                raiseSyntaxError m "(declare-enum LEAF TREE ... TREE)"
            "define-resource-type"
              | [(_, TreeLeaf name), discarder, copier] <- rest -> do
                name' <- withSectionPrefix name
                discarder' <- interpret discarder >>= discern
                copier' <- interpret copier >>= discern
                insertConstant m name'
                defList <- parse restStmtList
                return $ WeakStmtResourceType m name' discarder' copier' : defList
              | otherwise ->
                raiseSyntaxError m "(define-resource-type LEAF TREE TREE)"
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
                modify (\env -> env {nsEnv = (from, to) : (nsEnv env)})
                parse restStmtList
              | otherwise ->
                raiseSyntaxError m "(define-prefix LEAF LEAF)"
            "remove-prefix"
              | [(_, TreeLeaf from), (_, TreeLeaf to)] <- rest -> do
                modify (\env -> env {nsEnv = (filter (/= (from, to))) (nsEnv env)})
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
            "set-as-opaque"
              | [(_, TreeLeaf name)] <- rest -> do
                name' <- withSectionPrefix name
                name'' <- lookupTopLevelName m name'
                ss <- parse restStmtList
                return $ WeakStmtOpaque name'' : ss
              | otherwise ->
                raiseSyntaxError m "(set-as-opaque LEAF)"
            "set-as-data"
              | ((_, TreeLeaf name) : (_, TreeLeaf intStr) : constructorNameList) <- rest,
                Just i <- readMaybe (T.unpack intStr) -> do
                xs <- mapM (extractLeaf >=> withSectionPrefix) constructorNameList
                name' <- withSectionPrefix name
                modify (\env -> env {dataEnv = Map.insert name' xs (dataEnv env)})
                forM_ (zip xs [0 ..]) $ \(x, k) -> modify (\env -> env {constructorEnv = Map.insert x (i, k) (constructorEnv env)})
                parse restStmtList
              | otherwise -> do
                raiseSyntaxError m "(set-as-data LEAF INT LEAF*)"
            "statement" ->
              parse $ rest ++ restStmtList
            _ ->
              interpretAux headStmt restStmtList
        _ ->
          interpretAux headStmt restStmtList

interpretAux :: TreePlus -> [TreePlus] -> WithEnv [WeakStmt]
interpretAux headStmt restStmtList = do
  e <- interpret headStmt >>= discern
  h <- newIdentFromText "_"
  let m = metaOf e
  t <- newAster m
  defList <- parse restStmtList
  return $ WeakStmtDef m (m, h, t) e : defList

insertConstant :: Hint -> T.Text -> WithEnv ()
insertConstant m x = do
  cset <- gets constantSet
  if S.member x cset
    then raiseError m $ "the constant `" <> x <> "` is already defined"
    else modify (\env -> env {constantSet = S.insert x (constantSet env)})

insEnumEnv :: Hint -> T.Text -> [(T.Text, Int)] -> WithEnv ()
insEnumEnv m name xis = do
  eenv <- gets enumEnv
  let definedEnums = Map.keys eenv ++ map fst (concat (Map.elems eenv))
  case find (`elem` definedEnums) $ name : map fst xis of
    Just x ->
      raiseError m $ "the constant `" <> x <> "` is already defined [ENUM]"
    _ -> do
      let (xs, is) = unzip xis
      let rev = Map.fromList $ zip xs (zip (repeat name) is)
      modify
        ( \e ->
            e
              { enumEnv = Map.insert name xis (enumEnv e),
                revEnumEnv = rev `Map.union` revEnumEnv e
              }
        )

extractLeaf :: TreePlus -> WithEnv T.Text
extractLeaf t =
  case t of
    (_, TreeLeaf x) ->
      return x
    _ ->
      raiseSyntaxError (fst t) "LEAF"

lookupTopLevelName :: Hint -> T.Text -> WithEnv Ident
lookupTopLevelName m s = do
  nenv <- gets topNameEnv
  case Map.lookup s nenv of
    Nothing ->
      raiseError m $ "no such top-level variable defined: " <> s
    Just s' ->
      return s'
