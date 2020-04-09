{-# LANGUAGE OverloadedStrings #-}

module Parse.MacroExpand
  ( macroExpand
  , checkNotationSanity
  ) where

import Control.Monad.Except
import Control.Monad.State

import qualified Data.Set as S
import qualified Data.Text as T

import Data.Basic
import Data.Env
import Data.Tree

type MacroSubst = [(T.Text, TreePlus)]

macroExpand :: TreePlus -> WithEnv TreePlus
macroExpand t = recurM (macroExpand1 . splice) t

macroExpand' :: TreePlus -> WithEnv TreePlus
macroExpand' t = recurM (macroExpand1 . splice) t

recurM :: (Monad m) => (TreePlus -> m TreePlus) -> TreePlus -> m TreePlus
recurM f (m, TreeLeaf s) = f (m, TreeLeaf s)
recurM f (m, TreeNode ts) = do
  ts' <- mapM (recurM f) ts
  f (m, TreeNode ts')

macroExpand1 :: TreePlus -> WithEnv TreePlus
macroExpand1 t@(i, _) = do
  nenv <- gets notationEnv
  kenv <- gets keywordEnv
  -- the computation of atomListOf could be memoized
  if atomListOf t `S.disjoint` kenv
    then return t -- t is already resolved
    else do
      mMatch <- try (macroMatch t) nenv
      case mMatch of
        Just (sub, skel) -> macroExpand' $ applySubst sub $ replaceMeta i skel
        Nothing -> return t

type Notation = TreePlus

macroMatch ::
     TreePlus -- input tree
  -> Notation -- registered notation
  -> WithEnv (Maybe MacroSubst) -- {symbols in a pattern} -> {trees}
macroMatch t1@(_, TreeLeaf s1) (_, TreeLeaf s2) = do
  kenv <- gets keywordEnv
  case s2 `elem` kenv of
    True
      | s1 == s2 -> return $ Just []
      | otherwise -> return Nothing
    False -> return $ Just [(s2, t1)]
macroMatch t1@(_, TreeNode _) (_, TreeLeaf s2) = do
  kenv <- gets keywordEnv
  case s2 `elem` kenv of
    True -> return Nothing
    False -> return $ Just [(s2, t1)]
macroMatch (_, TreeLeaf _) (_, TreeNode _) = return Nothing
macroMatch (_, TreeNode []) (_, TreeNode []) = return $ Just []
macroMatch (_, TreeNode _) (_, TreeNode []) = return Nothing
macroMatch (_, TreeNode []) (_, TreeNode _) = return Nothing
macroMatch (m1, TreeNode ts1) (_, TreeNode ts2)
  | (_, TreeLeaf s2) <- last ts2
  , T.last s2 == '+' -- this ensures that s2 is not a keyword
  , length ts1 >= length ts2 = do
    let (xs, rest) = splitAt (length ts2 - 1) ts1
    let ys = take (length ts2 - 1) ts2
    mzs <- sequence <$> zipWithM macroMatch xs ys
    return $ mzs >>= \zs -> Just $ (s2, toSpliceTree m1 rest) : join zs
  | length ts1 == length ts2 = do
    mzs <- sequence <$> zipWithM macroMatch ts1 ts2
    return $ mzs >>= \zs -> Just $ join zs
  | otherwise = return Nothing

applySubst :: MacroSubst -> Notation -> TreePlus
applySubst sub (i, TreeLeaf s) = do
  case lookup s sub of
    Nothing -> (i, TreeLeaf s)
    Just t -> replaceMeta i t
applySubst sub (i, TreeNode ts) = (i, TreeNode $ map (applySubst sub) ts)

toSpliceTree :: Meta -> [TreePlus] -> TreePlus
toSpliceTree m ts = (m, TreeNode [(m, TreeLeaf "splice"), (m, TreeNode ts)])

checkNotationSanity :: Notation -> WithEnv ()
checkNotationSanity t = do
  checkKeywordCondition t
  checkPlusCondition t

checkKeywordCondition :: Notation -> WithEnv ()
checkKeywordCondition t = do
  kenv <- gets keywordEnv
  if not $ null $ kenv `S.intersection` atomListOf t
    then return ()
    else raiseError (fst t) "A notation must include at least one keyword"

checkPlusCondition :: Notation -> WithEnv ()
checkPlusCondition (m, TreeLeaf s) =
  if T.last s /= '+'
    then return ()
    else raiseError
           m
           "The '+'-suffixed name can be occurred only at the end of a list"
checkPlusCondition (_, TreeNode []) = return ()
checkPlusCondition (_, TreeNode ts) = do
  mapM_ checkPlusCondition $ init ts
  case last ts of
    (_, TreeLeaf _) -> return ()
    ts' -> checkPlusCondition ts'

splice :: TreePlus -> TreePlus
splice t = splice' t

-- (a b (splice (c (splice (p q)) e)) f) ~> (a b c p q d e)
splice' :: TreePlus -> TreePlus
splice' t@(_, TreeLeaf _) = t
splice' (m, TreeNode ts) = do
  let ts' = map splice' ts
  (m, TreeNode $ expandSplice $ map findSplice ts')

findSplice :: TreePlus -> Either TreePlus [TreePlus]
findSplice (_, TreeNode [(_, TreeLeaf "splice"), (_, TreeNode ts)]) = do
  Right ts
findSplice t = Left t

expandSplice :: [Either TreePlus [TreePlus]] -> [TreePlus]
expandSplice [] = []
expandSplice (Left t:rest) = t : expandSplice rest
expandSplice (Right ts:rest) = ts ++ expandSplice rest

-- returns the first "Just"
try :: (Monad m) => (a -> m (Maybe b)) -> [(a, c)] -> m (Maybe (b, c))
try _ [] = return Nothing
try f ((s, t):as) = do
  mx <- f s
  case mx of
    Nothing -> try f as
    Just x -> return $ Just (x, t)
