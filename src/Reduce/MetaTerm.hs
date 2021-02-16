module Reduce.MetaTerm where

import Data.Env
import Data.Ident
import qualified Data.IntMap as IntMap
import Data.MetaTerm
import Data.Tree

-- reduceMetaTerm :: MetaTermPlus -> WithEnv TreePlus
-- reduceMetaTerm e = do
--   e' <- reduceMetaTerm e
--   reifyMetaTerm e'

reduceMetaTerm :: MetaTermPlus -> WithEnv MetaTermPlus
reduceMetaTerm term =
  case term of
    (m, MetaTermImpElim e es) -> do
      e' <- reduceMetaTerm e
      es' <- mapM reduceMetaTerm es
      case e' of
        (_, MetaTermImpIntro xs body)
          | length xs == length es' -> do
            let sub = IntMap.fromList $ zip (map asInt xs) es'
            reduceMetaTerm $ substMetaTerm sub body
        _ ->
          raiseError m "arity mismatch"
    (_, MetaTermNecElim e) -> do
      e' <- reduceMetaTerm e
      case e' of
        (_, MetaTermNecIntro e'') ->
          reduceMetaTerm e''
        (m, _) ->
          raiseError m "the inner term of an unquote must be a quoted term"
    (m, MetaTermNode es) -> do
      es' <- mapM reduceMetaTerm es
      return (m, MetaTermNode es')
    _ ->
      return term

reifyMetaTerm :: MetaTermPlus -> WithEnv TreePlus
reifyMetaTerm term =
  case term of
    (m, MetaTermLeaf x) ->
      return (m, TreeLeaf x)
    (m, MetaTermNode es) -> do
      es' <- mapM reifyMetaTerm es
      return (m, TreeNode es')
    (m, _) ->
      raiseError m $ "the result of meta computation must be an AST, but is: \n" <> showAsSExp (reifyMetaTerm' term)

reifyMetaTerm' :: MetaTermPlus -> TreePlus
reifyMetaTerm' term =
  case term of
    (m, MetaTermVar x) ->
      (m, TreeLeaf $ asText' x) -- ホントはmeta専用の名前にするべき
    (m, MetaTermImpIntro xs e) -> do
      let e' = reifyMetaTerm' e
      let xs' = map (\i -> (m, TreeLeaf $ asText' i)) xs
      (m, TreeNode [(m, TreeLeaf "LAMBDA"), (m, TreeNode xs'), e'])
    (m, MetaTermImpElim e es) -> do
      let e' = reifyMetaTerm' e
      let es' = map reifyMetaTerm' es
      (m, TreeNode ((m, TreeLeaf "APPLY") : e' : es'))
    (m, MetaTermNecIntro e) -> do
      let e' = reifyMetaTerm' e
      (m, TreeNode [(m, TreeLeaf "QUOTE"), e'])
    (m, MetaTermNecElim e) -> do
      let e' = reifyMetaTerm' e
      (m, TreeNode [(m, TreeLeaf "UNQUOTE"), e'])
    (m, MetaTermLeaf x) ->
      (m, TreeLeaf x)
    (m, MetaTermNode es) -> do
      let es' = map reifyMetaTerm' es
      (m, TreeNode es')
