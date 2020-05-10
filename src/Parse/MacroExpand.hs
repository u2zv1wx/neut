module Parse.MacroExpand
  ( macroExpand,
    checkNotationSanity,
  )
where

import Control.Monad.State.Lazy
import Data.Env
import Data.Meta
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Tree

type MacroSubst = [(T.Text, TreePlus)]

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
  kenv <- gets keywordEnv
  if atomListOf t `S.disjoint` kenv
    then return t -- t is already resolved
    else do
      mMatch <- try (macroMatch t) nenv
      case mMatch of
        Just (sub, skel) ->
          macroExpand $ applySubst sub $ replaceMeta i skel
        Nothing ->
          return t

type Notation =
  TreePlus

macroMatch ::
  TreePlus -> -- input tree
  Notation -> -- registered notation
  WithEnv (Maybe MacroSubst) -- {symbols in a pattern} -> {trees}
macroMatch t1 t2 =
  case (t1, t2) of
    ((_, TreeLeaf s1), (_, TreeLeaf s2)) -> do
      kenv <- gets keywordEnv
      case s2 `elem` kenv of
        True
          | s1 == s2 ->
            return $ Just []
          | otherwise ->
            return Nothing
        False ->
          return $ Just [(s2, t1)]
    ((_, TreeNode _), (_, TreeLeaf s2)) -> do
      kenv <- gets keywordEnv
      case s2 `elem` kenv of
        True ->
          return Nothing
        False ->
          return $ Just [(s2, t1)]
    ((_, TreeLeaf _), (_, TreeNode _)) ->
      return Nothing
    ((_, TreeNode []), (_, TreeNode [])) ->
      return $ Just []
    ((_, TreeNode _), (_, TreeNode [])) ->
      return Nothing
    ((_, TreeNode []), (_, TreeNode _)) ->
      return Nothing
    ((m1, TreeNode ts1), (_, TreeNode ts2))
      | (_, TreeLeaf s2) <- last ts2,
        T.last s2 == '+',
        length ts1 >= length ts2 -> do
        let (xs, rest) = splitAt (length ts2 - 1) ts1
        let ys = take (length ts2 - 1) ts2
        mzs <- sequence <$> zipWithM macroMatch xs ys
        return $ mzs >>= \zs -> Just $ (s2, toSpliceTree m1 rest) : join zs
      | length ts1 == length ts2 -> do
        mzs <- sequence <$> zipWithM macroMatch ts1 ts2
        return $ mzs >>= \zs -> Just $ join zs
      | otherwise ->
        return Nothing

applySubst :: MacroSubst -> Notation -> TreePlus
applySubst sub notationTree =
  case notationTree of
    (i, TreeLeaf s) ->
      case lookup s sub of
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

checkNotationSanity :: Notation -> WithEnv ()
checkNotationSanity t = do
  checkPlusCondition t
  notationName <- extractHeadAtom t
  modify (\e -> e {keywordEnv = S.insert notationName (keywordEnv e)})

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

splice :: TreePlus -> TreePlus
splice =
  splice'

-- (a b (splice (c (splice (p q)) e)) f) ~> (a b c p q d e)
splice' :: TreePlus -> TreePlus
splice' tree =
  case tree of
    t@(_, TreeLeaf _) ->
      t
    (m, TreeNode ts) -> do
      let ts' = map splice' ts
      (m, TreeNode $ expandSplice $ map findSplice ts')

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

-- returns the first "Just"
try :: (Monad m) => (a -> m (Maybe b)) -> [(a, c)] -> m (Maybe (b, c))
try f candidateList =
  case candidateList of
    [] ->
      return Nothing
    ((s, t) : as) -> do
      mx <- f s
      case mx of
        Nothing ->
          try f as
        Just x ->
          return $ Just (x, t)
