module Reduce.MetaCST
  ( reduceMetaCST,
  )
where

import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.MetaAST
import Data.Tree

reduceMetaCST :: MetaCSTPlus -> WithEnv TreePlus
reduceMetaCST term =
  case term of
    (m, MetaCSTLeaf x) ->
      return (m, TreeLeaf x)
    (m, MetaCSTNode ts) -> do
      ts' <- mapM reduceMetaCST ts
      return (m, TreeNode ts')
    (m, MetaCSTUnquote e) -> do
      e' <- reduceMetaAST' e
      case e' of
        (_, MetaASTQuote t) ->
          reduceMetaCST t
        _ ->
          raiseError m "ill-formed term"

reduceMetaAST' :: MetaASTPlus -> WithEnv MetaASTPlus
reduceMetaAST' term =
  case term of
    (m, MetaASTApp e es) -> do
      e' <- reduceMetaAST' e
      es' <- mapM reduceMetaAST' es
      case e' of
        (_, MetaASTAbs xs body)
          | length xs == length es' -> do
            let sub = Map.fromList $ zip xs es'
            reduceMetaAST' $ substMetaAST sub body
          | otherwise ->
            raiseError m "arity mismatch"
        _ ->
          raiseError m "ill-formed term"
    (m, MetaASTQuote t) -> do
      t' <- reduceMetaCST' t
      return (m, MetaASTQuote t')
    _ ->
      return term

reduceMetaCST' :: MetaCSTPlus -> WithEnv MetaCSTPlus
reduceMetaCST' term =
  case term of
    (_, MetaCSTLeaf _) ->
      return term
    (m, MetaCSTNode ts) -> do
      ts' <- mapM reduceMetaCST' ts
      return (m, MetaCSTNode ts')
    (m, MetaCSTUnquote e) -> do
      e' <- reduceMetaAST' e
      case e' of
        (_, MetaASTQuote t) ->
          reduceMetaCST' t
        _ ->
          raiseError m "ill-formed term"
