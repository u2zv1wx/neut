module Parse.MacroExpand
  ( macroExpand
  , checkNotation
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.List (intersect)

import Data.Basic
import Data.Env
import Data.Maybe (fromMaybe)
import Data.Tree

type MacroSubst = [(String, TreePlus)]

-- CBV-like macro expansion
macroExpand :: TreePlus -> WithEnv TreePlus
macroExpand t = recurM (macroExpand1 . splice) t

recurM :: (Monad m) => (TreePlus -> m TreePlus) -> TreePlus -> m TreePlus
recurM f (m, TreeAtom s) = f (m, TreeAtom s)
recurM f (m, TreeNode ts) = do
  ts' <- mapM (recurM f) ts
  f (m, TreeNode ts')

macroExpand1 :: TreePlus -> WithEnv TreePlus
macroExpand1 t@(i, _) = do
  nenv <- gets notationEnv
  mMatch <- try (macroMatch t) nenv
  case mMatch of
    Just (subst, (_, template)) ->
      macroExpand $ applyMacroSubst subst (i, template)
    Nothing -> return t

type Pattern = TreePlus

macroMatch ::
     TreePlus -- input tree
  -> Pattern -- registered notation
  -> WithEnv (Maybe MacroSubst) -- {symbols in a pattern} -> {trees}
macroMatch t1@(_, TreeAtom s1) (_, TreeAtom s2) = do
  kenv <- gets keywordEnv
  case s2 `elem` kenv of
    True
      | s1 == s2 -> return $ Just []
      | otherwise -> return Nothing
    False -> return $ Just [(s2, t1)]
macroMatch t1 (_, TreeAtom s2) = do
  kenv <- gets keywordEnv
  case s2 `elem` kenv of
    True -> return Nothing
    False -> return $ Just [(s2, t1)]
macroMatch (_, TreeAtom _) (_, TreeNode _) = return Nothing
macroMatch (_, TreeNode []) (_, TreeNode []) = return $ Just []
macroMatch _ (_, TreeNode []) = return Nothing
macroMatch (_, TreeNode ts1) (_, TreeNode ts2)
  | (_, TreeAtom sym) <- last ts2
  , last sym == '+'
  , length ts1 >= length ts2 = do
    let (xs, rest) = splitAt (length ts2 - 1) ts1
    let ys = take (length ts2 - 1) ts2
    mzs <- sequence <$> zipWithM macroMatch xs ys
    return $ mzs >>= \zs -> Just $ (sym, toSpliceTree rest) : join zs
  | length ts1 == length ts2 = do
    mzs <- sequence <$> zipWithM macroMatch ts1 ts2
    return $ mzs >>= \zs -> Just $ join zs
  | otherwise = return Nothing

applyMacroSubst :: MacroSubst -> Pattern -> TreePlus
applyMacroSubst sub (i, TreeAtom s) = fromMaybe (i, TreeAtom s) (lookup s sub)
applyMacroSubst sub (i, TreeNode ts) =
  (i, TreeNode $ map (applyMacroSubst sub) ts)

toSpliceTree :: [TreePlus] -> TreePlus
toSpliceTree ts =
  ( emptyMeta
  , TreeNode [(emptyMeta, TreeAtom "splice"), (emptyMeta, TreeNode ts)])

checkNotation :: Pattern -> WithEnv ()
checkNotation t = do
  checkKeywordCondition t
  checkPlusCondition t

checkKeywordCondition :: Pattern -> WithEnv ()
checkKeywordCondition t = do
  kenv <- gets keywordEnv
  if not $ null $ kenv `intersect` atomListOf t
    then return ()
    else throwError "A notation must include at least one keyword"

checkPlusCondition :: Pattern -> WithEnv ()
checkPlusCondition (_, TreeAtom s) =
  if last s /= '+'
    then return ()
    else throwError
           "The '+'-suffixed name can be occurred only at the end of a list"
checkPlusCondition (_, TreeNode []) = return ()
checkPlusCondition (_, TreeNode ts) = do
  mapM_ checkPlusCondition $ init ts
  case last ts of
    (_, TreeAtom _) -> return ()
    ts' -> checkPlusCondition ts'

-- (a b (splice (c (splice (p q)) e)) f) ~> (a b c p q d e)
splice :: TreePlus -> TreePlus
splice t@(_, TreeAtom _) = t
splice (m, TreeNode ts) = do
  let ts' = map splice ts
  (m, TreeNode $ expandSplice $ map findSplice ts')

findSplice :: TreePlus -> Either TreePlus [TreePlus]
findSplice (_, TreeNode [(_, TreeAtom "splice"), (_, TreeNode ts)]) = do
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
