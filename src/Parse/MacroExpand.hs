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

-- type MacroSubst = ([(String, TreePlus)], [(String, [TreePlus])])
type Pattern = TreePlus

-- CBV-like macro expansion
macroExpand :: TreePlus -> WithEnv TreePlus
macroExpand t = recurM (macroExpand1 . splice) t

recurM :: (Monad m) => (TreePlus -> m TreePlus) -> TreePlus -> m TreePlus
recurM f (m, TreeAtom s) = f (m, TreeAtom s)
recurM f (m, TreeNode ts) = do
  ts' <- mapM (recurM f) ts
  f (m, TreeNode ts')

-- Given a S-expression, check if the expression matches one of the registered
-- notations.
--   (1) If a match (that is, a pair of substitution and "macro template") is found,
--   replace the holes in the template by the substitution, and recursively try to
--   macro-expand the resulting expression.
--   (2) If the S-expression doesn't match with any registered notations, just return
--   the S-expression itself.
macroExpand1 :: TreePlus -> WithEnv TreePlus
macroExpand1 t@(i, _) = do
  nenv <- gets notationEnv
  mMatch <- try (macroMatch t) nenv
  case mMatch of
    Just (subst, (_, template)) ->
      macroExpand $ applyMacroSubst subst (i, template)
    Nothing -> return t

-- returns the first "Just"
try :: (Monad m) => (a -> m (Maybe b)) -> [(a, c)] -> m (Maybe (b, c))
try _ [] = return Nothing
try f ((s, t):as) = do
  mx <- f s
  case mx of
    Nothing -> try f as
    Just x -> return $ Just (x, t)

-- `macroMatch` determines the behavior of matching.
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

-- macroMatch (_, TreeNode ts1) (_, TreeNode ts2)
--   -- The input is list of S-expressions, and also the pattern is.
--   -- We fistly check that the last element of `ts2` is an atom with a name that
--   -- ends by '+'. We regard such a names as a name of multiple S-expressions.
--   --
--   -- For example, suppose that the input is `(e1 2 3 foo 5)` and the pattern is
--   -- `(e1 2 rest+)`. In this case, the `rest+` should be matched to the list [3, foo, 5].
--   -- This behavior is indispensable when we realize practical macros.
--   -- Note that the [3, foo, 5] is not the same as (3 foo 5). the `[3, foo, 5]` is the
--   -- list in the meta-language (namely, Haskell), whereas the `(3 foo 5)` is the list
--   -- in the object-language (namely, QuasiTerm).
--  = do
--   case last ts2 of
--     (_, TreeAtom sym)
--       | last sym == '+'
--       , length ts1 >= length ts2
--       -- If the last element is such a '+'-suffixed name, we'll try to generate a substitution
--       -- as in the example above. We check that the length of `ts2` is the same or greater
--       -- than that of `ts1`, so that we can exclude an improper cases such as
--       -- `ts1 == (1 2 3)` and `ts2 == (1 2 3 4 rest+)`. From here, as a running example,
--       -- let us take `ts1 == (1 2 3 4 5)` and `ts2 == (pat1 pat2 rest+)`. We take the first
--       -- (length ts2 - 1) elements from `ts1`, obtaining `(1 2)`. We also take the
--       -- first (length ts2 - 1) elements from `ts2`, obtaining `(pat1 pat2)`.
--       -- We then match `(1 2)` and `(pat1 pat2)` in the pairwise way, obtaining some
--       -- substitution. As for the last element, we generate a substitution from the
--       -- last element of `ts2`, namely `rest+`, to the remaining elements of `ts1`, namely
--       -- `[3, 4, 5]`. Finally, we combine these results and return it.
--        -> do
--         let (xs, rest) = splitAt (length ts2 - 1) ts1
--         let ys = take (length ts2 - 1) ts2
--         mzs <- sequence <$> zipWithM macroMatch xs ys
--         return $
--           mzs >>= \zs -> do
--             let t = toSpliceTree rest
--             Just $ (sym, t) : join zs
--     _
--       | length ts1 == length ts2
--       -- If the last element is not a '+'-suffixed name, the `ts1` and `ts2` must be
--       -- strictly matched. So we just try to match them in the pairwise way, and return
--       -- the resulting substitutions.
--        -> do
--         mzs <- sequence <$> zipWithM macroMatch ts1 ts2
--         return $ mzs >>= \zs -> Just $ join zs
--     _ -> return Nothing
-- Using the resulting substitution, replace the variables in a pattern.
-- The first projection of MacroSubst is an "ordinary" substitution, namely just a
-- mapping from a name to a tree. The second projection is a "multiple" substitution,
-- namely a mapping from a name to a list of trees.
applyMacroSubst :: MacroSubst -> Pattern -> TreePlus
-- applyMacroSubst (s1, _) (i, TreeAtom s) =
applyMacroSubst sub (i, TreeAtom s) = fromMaybe (i, TreeAtom s) (lookup s sub)
applyMacroSubst sub (i, TreeNode ts) =
  (i, TreeNode $ map (applyMacroSubst sub) ts)

toSpliceTree :: [TreePlus] -> TreePlus
toSpliceTree ts =
  ( emptyMeta
  , TreeNode [(emptyMeta, TreeAtom "splice"), (emptyMeta, TreeNode ts)])

-- applyMacroSubst sub@(_, s2) (i, TreeNode ts)
--   -- When we need to replace the last variable of a list, we check if the variable
--   -- is a '+'-suffixed one. If it is, we lookup the list of trees from the
--   -- substitution `sub` by the '+'-suffixed name, and concatenate the list of
--   -- trees to the end of the list. For example, if `ts == (e1 e2 rest+)`, we lookup
--   -- the `sub` by "rest+". Suppose that we found a list `[3 4 5]`.
--   -- Then, after applying the substitution to `e1` and `e2` recursively, obtaining
--   -- `e1'` and `e2'` respectively, we append the `[3 4 5]` to `(e1' e2')`, obtaining
--   -- (e1' e2' 3 4 5).
--   -- assuming x+ ~> (e1 e2 e3), subst (p q x r s) ~> (p q e1 e2 e3 r s)
--   -- (not (p q x r s) > (p q (e1 e2 e3) r s))
--  =
--   case last ts -- これlastをとってるのおかしくね、ってわけだ。
--         of
--     (j, TreeAtom s)
--       | last s == '+'
--       , s `elem` map fst s2 -> do
--         let ts' = map (applyMacroSubst sub) (take (length ts - 1) ts)
--         case lookup s s2 of
--           Nothing -> (j, TreeNode (ts' ++ [(j, TreeAtom s)]))
--           Just rest -> (i, TreeNode (ts' ++ rest))
--     _ -> do
--       let ts' = map (applyMacroSubst sub) ts
--       (i, TreeNode ts')
-- The '+'-suffixed name can be occurred only at the end of a list
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
