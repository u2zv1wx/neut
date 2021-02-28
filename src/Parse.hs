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
import Parse.Rule

parse :: [TreePlus] -> WithEnv [WeakStmt]
parse stmtTreeList =
  case stmtTreeList of
    [] ->
      return []
    headStmt : restStmtList -> do
      case headStmt of
        (m, TreeNode (leaf@(_, TreeLeaf headAtom) : rest)) ->
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
            "data"
              | name@(mFun, TreeLeaf _) : xts@(_, TreeNode _) : es' <- rest ->
                parse $ (m, TreeNode [leaf, (mFun, TreeNode (name : xts : es'))]) : restStmtList
              | otherwise -> do
                stmtList1 <- parseData m rest
                stmtList2 <- parse restStmtList
                return $ stmtList1 ++ stmtList2
            "record"
              | (_, TreeLeaf _) : (_, TreeNode _) : _ <- rest -> do
                rest' <- asData m rest
                stmtList1 <- parseData m [rest']
                stmtList2 <- generateProjections rest'
                stmtList3 <- parse restStmtList
                return $ stmtList1 ++ stmtList2 ++ stmtList3
              | otherwise ->
                raiseSyntaxError m "(record name (TREE ... TREE) TREE ... TREE)"
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
