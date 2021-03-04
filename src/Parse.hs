module Parse
  ( parse,
  )
where

import Control.Monad.State.Lazy hiding (get)
import Data.Basic
import Data.Env
import Data.Log
import Data.Namespace
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Tree
import Data.WeakTerm
import Parse.Discern
import Parse.Interpret

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
            "let"
              | [xt, e] <- rest -> do
                e' <- interpret e >>= discern
                xt' <- prefixTextPlus xt >>= interpretIdentPlus >>= discernIdentPlus
                defList <- parse restStmtList
                return $ WeakStmtLet m xt' e' : defList
              | otherwise ->
                raiseSyntaxError m "(let LEAF TREE TREE) | (let TREE TREE)"
            "declare-constant"
              | [(_, TreeLeaf name), t] <- rest -> do
                t' <- interpret t >>= discern
                name' <- withSectionPrefix name
                insertConstant m name'
                defList <- parse restStmtList
                return $ WeakStmtConstDecl (m, name', t') : defList
              | otherwise ->
                raiseSyntaxError m "(declare-constant LEAF TREE)"
            "define-resource-type"
              | [(_, TreeLeaf name), discarder, copier] <- rest -> do
                name' <- withSectionPrefix name
                discarder' <- interpret discarder >>= discern
                copier' <- interpret copier >>= discern
                ensureClosedness discarder'
                ensureClosedness copier'
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
            "statement" ->
              parse $ rest ++ restStmtList
            _ ->
              interpretAux headStmt restStmtList
        _ ->
          interpretAux headStmt restStmtList

interpretAux :: TreePlus -> [TreePlus] -> WithEnv [WeakStmt]
interpretAux headStmt restStmtList = do
  e <- interpret headStmt >>= discern
  h <- newNameWith'' "_"
  let m = metaOf e
  t <- newAster m
  defList <- parse restStmtList
  return $ WeakStmtLet m (m, h, t) e : defList

insertConstant :: Hint -> T.Text -> WithEnv ()
insertConstant m x = do
  cset <- gets constantSet
  if S.member x cset
    then raiseError m $ "the constant `" <> x <> "` is already defined"
    else modify (\env -> env {constantSet = S.insert x (constantSet env)})

showFreeVariables :: S.Set Ident -> T.Text
showFreeVariables s =
  T.intercalate ", " $ map asText $ S.toList s

ensureClosedness :: WeakTermPlus -> WithEnv ()
ensureClosedness e = do
  let varSet = varWeakTermPlus e
  when (not (S.null varSet)) $
    raiseError (fst e) $ "the term here must be closed, but actually contains: " <> showFreeVariables varSet
