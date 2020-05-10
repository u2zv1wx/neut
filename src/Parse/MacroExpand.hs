module Parse.MacroExpand
  ( macroExpand,
    checkNotationSanity,
  )
where

import Control.Monad.State.Lazy
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Meta
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Tree

type MacroSubst = Map.HashMap T.Text TreePlus

macroExpand :: TreePlus -> WithEnv TreePlus
macroExpand =
  recurM (stepExpand . splice)

recurM :: (Monad m) => (TreePlus -> m TreePlus) -> TreePlus -> m TreePlus
recurM f tree =
  case tree of
    (m, TreeLeaf s) ->
      f (m, TreeLeaf s)
    (m, TreeNode ts) -> do
      ts' <- mapM (recurM f) ts
      f (m, TreeNode ts')

stepExpand :: TreePlus -> WithEnv TreePlus
stepExpand t@(i, _) = do
  nenv <- gets notationEnv
  case headAtomOf t of
    Just headAtom
      | Just nenv' <- Map.lookup headAtom nenv,
        Just (sub, skel) <- try (macroMatch t) nenv' ->
        macroExpand $ applySubst sub $ replaceMeta i skel
    _ ->
      return t

type Notation =
  TreePlus

macroMatch ::
  TreePlus -> -- input tree
  Notation -> -- registered notation
  Maybe MacroSubst -- {symbols in a pattern} -> {trees}
macroMatch t1 t2 =
  case (t1, t2) of
    ((_, TreeLeaf s1), (_, TreeLeaf s2))
      | s1 == s2 ->
        return Map.empty
      | otherwise ->
        Nothing
    ((_, TreeNode _), (_, TreeLeaf _)) ->
      Nothing
    ((_, TreeLeaf _), (_, TreeNode _)) ->
      Nothing
    ((_, TreeNode ts1), (_, TreeNode ts2)) ->
      case (ts1, ts2) of
        ((_, TreeLeaf s1) : rest1, (_, TreeLeaf s2) : rest2)
          | s1 == s2 ->
            macroMatch' rest1 rest2
        _ ->
          Nothing

macroMatch' :: [TreePlus] -> [TreePlus] -> Maybe MacroSubst
macroMatch' ts1 ts2 =
  case (ts1, ts2) of
    (_, [(_, TreeLeaf s2)])
      | T.last s2 == '+',
        length ts1 > 0 -> do
        let m1 = fst (head ts1)
        return $ Map.singleton s2 $ toSpliceTree m1 ts1
    ([], []) ->
      return Map.empty
    (_ : _, []) ->
      Nothing
    ([], _ : _) ->
      Nothing
    (t1 : rest1, t2 : rest2) -> do
      sub1 <- macroMatch'' t1 t2
      sub2 <- macroMatch' rest1 rest2
      return $ Map.union sub1 sub2

macroMatch'' :: TreePlus -> TreePlus -> Maybe MacroSubst
macroMatch'' t1 t2 =
  case (t1, t2) of
    ((_, TreeLeaf _), (_, TreeLeaf x)) ->
      return $ Map.singleton x t1
    ((_, TreeNode _), (_, TreeLeaf x)) ->
      return $ Map.singleton x t1
    ((_, TreeLeaf _), (_, TreeNode _)) ->
      Nothing
    ((_, TreeNode ts1), (_, TreeNode ts2)) ->
      macroMatch' ts1 ts2

applySubst :: MacroSubst -> Notation -> TreePlus
applySubst sub notationTree =
  case notationTree of
    (i, TreeLeaf s) ->
      case Map.lookup s sub of
        Nothing ->
          (i, TreeLeaf s)
        Just t ->
          replaceMeta i t
    (i, TreeNode ts) ->
      (i, TreeNode $ map (applySubst sub) ts)

toSpliceTree :: Meta -> [TreePlus] -> TreePlus
toSpliceTree m ts =
  (m, TreeNode [(m, TreeLeaf "splice"), (m, TreeNode ts)])

extractHeadAtom :: TreePlus -> WithEnv T.Text
extractHeadAtom tree@(m, _) =
  case tree of
    (_, TreeLeaf atom) -> do
      checkKeywordSanity m atom
      return atom
    (_, TreeNode ((_, TreeLeaf atom) : _)) -> do
      checkKeywordSanity m atom
      return atom
    _ ->
      raiseError m "malformed notation"

checkKeywordSanity :: Meta -> T.Text -> WithEnv ()
checkKeywordSanity m x
  | x == "" =
    raiseError m "empty string for a keyword"
  | T.last x == '+' =
    raiseError m "A +-suffixed name cannot be a keyword"
  | otherwise =
    return ()

checkNotationSanity :: Notation -> WithEnv T.Text
checkNotationSanity t = do
  checkPlusCondition t
  notationName <- extractHeadAtom t
  modify (\e -> e {keywordEnv = S.insert notationName (keywordEnv e)})
  return notationName

checkPlusCondition :: Notation -> WithEnv ()
checkPlusCondition notationTree =
  case notationTree of
    (m, TreeLeaf s) ->
      if T.last s /= '+'
        then return ()
        else
          raiseError
            m
            "The '+'-suffixed name can be occurred only at the end of a list"
    (_, TreeNode []) ->
      return ()
    (_, TreeNode ts) -> do
      mapM_ checkPlusCondition $ init ts
      case last ts of
        (_, TreeLeaf _) ->
          return ()
        ts' ->
          checkPlusCondition ts'

-- (a b (splice (c (splice (p q)) e)) f) ~> (a b c p q d e)
splice :: TreePlus -> TreePlus
splice tree =
  case tree of
    t@(_, TreeLeaf _) ->
      t
    (m, TreeNode ts) ->
      (m, TreeNode $ expandSplice $ map (findSplice . splice) ts)

findSplice :: TreePlus -> Either TreePlus [TreePlus]
findSplice tree =
  case tree of
    (_, TreeNode [(_, TreeLeaf "splice"), (_, TreeNode ts)]) ->
      Right ts
    t ->
      Left t

expandSplice :: [Either TreePlus [TreePlus]] -> [TreePlus]
expandSplice itemList =
  case itemList of
    [] ->
      []
    Left t : rest ->
      t : expandSplice rest
    Right ts : rest ->
      ts ++ expandSplice rest

try :: (a -> Maybe b) -> [(a, c)] -> Maybe (b, c)
try f candidateList =
  case candidateList of
    [] ->
      Nothing
    ((s, t) : as) ->
      case f s of
        Nothing ->
          try f as
        Just x ->
          return (x, t)
