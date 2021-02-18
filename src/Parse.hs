module Parse
  ( parse,
  )
where

import Control.Monad.State.Lazy hiding (get)
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Hint
import Data.Ident
import Data.MetaTerm
import Data.Namespace
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Tree
import Data.WeakTerm
import Parse.Discern
import Parse.Interpret
import Parse.Rule
import Preprocess.Reflect

parse :: [TreePlus] -> WithEnv [WeakStmt]
parse stmtTreeList =
  case stmtTreeList of
    [] ->
      return []
    headStmt : restStmtList -> do
      case headStmt of
        (m, TreeNode (leaf@(_, TreeLeaf headAtom) : rest)) ->
          case headAtom of
            "constant"
              | [(_, TreeLeaf name), t] <- rest -> do
                t' <- interpret t >>= discern
                name' <- withSectionPrefix name
                insertConstant m name'
                defList <- parse restStmtList
                return $ WeakStmtConstDecl (m, name', t') : defList
              | otherwise ->
                raiseSyntaxError m "(constant LEAF TREE)"
            "end"
              | [(_, TreeLeaf s)] <- rest -> do
                ns <- gets sectionEnv
                case ns of
                  [] ->
                    raiseError m "there is no section to end"
                  s' : ns'
                    | s == s' -> do
                      getCurrentSection >>= unuse
                      modify (\e -> e {sectionEnv = ns'})
                      parse restStmtList
                    | otherwise ->
                      raiseError m $
                        "the innermost section is not `" <> s <> "`, but is `" <> s' <> "`"
              | otherwise ->
                raiseSyntaxError m "(end LEAF)"
            "enum"
              | (_, TreeLeaf name) : ts <- rest -> do
                xis <- reflectEnumItem m name $ map embed ts
                insEnumEnv m name xis
                parse restStmtList
              | otherwise ->
                raiseSyntaxError m "(enum LEAF TREE ... TREE)"
            "erase"
              | [(ms, TreeLeaf s)] <- rest -> do
                nenv <- gets topNameEnv
                s' <- asText <$> discernText ms s
                modify (\env -> env {topNameEnv = Map.filterWithKey (\k _ -> k /= s') nenv})
                parse restStmtList
              | otherwise ->
                raiseSyntaxError m "(erase LEAF)"
            "data"
              | name@(mFun, TreeLeaf _) : xts@(_, TreeNode _) : es' <- rest ->
                parse $ (m, TreeNode [leaf, (mFun, TreeNode (name : xts : es'))]) : restStmtList
              | otherwise -> do
                stmtList1 <- parseData m rest
                stmtList2 <- parse restStmtList
                return $ stmtList1 ++ stmtList2
            "let"
              | [(mx, TreeLeaf x), t, e] <- rest -> do
                let xt = (mx, TreeNode [(mx, TreeLeaf x), t])
                parse ((m, TreeNode [(m, TreeLeaf "let"), xt, e]) : restStmtList)
              | [xt, e] <- rest -> do
                e' <- interpret e >>= discern
                xt' <- prefixTextPlus xt >>= interpretIdentPlus >>= discernIdentPlus
                defList <- parse restStmtList
                return $ WeakStmtLet m xt' e' : defList
              | otherwise ->
                raiseSyntaxError m "(let LEAF TREE TREE) | (let TREE TREE)"
            "record"
              | (_, TreeLeaf _) : (_, TreeNode _) : _ <- rest -> do
                rest' <- asData m rest
                stmtList1 <- parseData m [rest']
                stmtList2 <- generateProjections rest'
                stmtList3 <- parse restStmtList
                return $ stmtList1 ++ stmtList2 ++ stmtList3
              | otherwise ->
                raiseSyntaxError m "(record name (TREE ... TREE) TREE ... TREE)"
            "section"
              | [(_, TreeLeaf s)] <- rest -> do
                modify (\e -> e {sectionEnv = s : sectionEnv e})
                getCurrentSection >>= use
                parse restStmtList
              | otherwise ->
                raiseSyntaxError m "(section LEAF)"
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

use :: T.Text -> WithEnv ()
use s =
  modify (\e -> e {prefixEnv = s : prefixEnv e})

unuse :: T.Text -> WithEnv ()
unuse s =
  modify (\e -> e {prefixEnv = filter (/= s) (prefixEnv e)})

withSectionPrefix :: T.Text -> WithEnv T.Text
withSectionPrefix x = do
  ns <- gets sectionEnv
  return $ foldl (\acc n -> n <> nsSep <> acc) x ns

getCurrentSection :: WithEnv T.Text
getCurrentSection = do
  ns <- gets sectionEnv
  return $ getCurrentSection' ns

getCurrentSection' :: [T.Text] -> T.Text
getCurrentSection' nameStack =
  case nameStack of
    [] ->
      ""
    [n] ->
      n
    (n : ns) ->
      getCurrentSection' ns <> nsSep <> n

prefixTextPlus :: TreePlus -> WithEnv TreePlus
prefixTextPlus tree =
  case tree of
    (m, TreeLeaf "_") -> do
      h <- newTextWith "_"
      return (m, TreeLeaf h)
    (m, TreeLeaf x) -> do
      x' <- withSectionPrefix x
      return (m, TreeLeaf x')
    (m, TreeNode [(mx, TreeLeaf "_"), t]) ->
      return (m, TreeNode [(mx, TreeLeaf "_"), t])
    (m, TreeNode [(mx, TreeLeaf x), t]) -> do
      x' <- withSectionPrefix x
      return (m, TreeNode [(mx, TreeLeaf x'), t])
    t ->
      raiseSyntaxError (fst t) "LEAF | (LEAF TREE)"

insertConstant :: Hint -> T.Text -> WithEnv ()
insertConstant m x = do
  cset <- gets constantSet
  if S.member x cset
    then raiseError m $ "the constant `" <> x <> "` is already defined"
    else modify (\env -> env {constantSet = S.insert x (constantSet env)})
