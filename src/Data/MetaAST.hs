module Data.MetaAST where

import qualified Data.HashMap.Lazy as Map
import Data.Hint
import qualified Data.Text as T

data MetaAST
  = MetaASTVar T.Text
  | MetaASTAbs [T.Text] MetaASTPlus
  | MetaASTApp MetaASTPlus [MetaASTPlus]
  | MetaASTQuote MetaCSTPlus
  deriving (Show)

type MetaASTPlus = (Hint, MetaAST)

data MetaCST
  = MetaCSTLeaf T.Text
  | MetaCSTNode [MetaCSTPlus]
  | MetaCSTUnquote MetaASTPlus
  deriving (Show)

type MetaCSTPlus = (Hint, MetaCST)

type SubstMetaAST =
  Map.HashMap T.Text MetaASTPlus

substMetaAST :: SubstMetaAST -> MetaASTPlus -> MetaASTPlus
substMetaAST sub term =
  case term of
    (_, MetaASTVar x) ->
      case Map.lookup x sub of
        Nothing ->
          term
        Just e ->
          e
    (m, MetaASTAbs xs e) -> do
      let sub' = foldr Map.delete sub xs
      let e' = substMetaAST sub' e
      (m, MetaASTAbs xs e')
    (m, MetaASTApp e es) -> do
      let e' = substMetaAST sub e
      let es' = map (substMetaAST sub) es
      (m, MetaASTApp e' es')
    (m, MetaASTQuote t) -> do
      let t' = substMetaCST sub t
      (m, MetaASTQuote t')

substMetaCST :: SubstMetaAST -> MetaCSTPlus -> MetaCSTPlus
substMetaCST sub tree =
  case tree of
    (_, MetaCSTLeaf _) ->
      tree
    (m, MetaCSTNode ts) -> do
      let ts' = map (substMetaCST sub) ts
      (m, MetaCSTNode ts')
    (m, MetaCSTUnquote e) -> do
      let e' = substMetaAST sub e
      (m, MetaCSTUnquote e')
