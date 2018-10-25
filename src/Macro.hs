module Macro
  ( macroExpand
  , isSaneNotation
  ) where

import Control.Monad
import Control.Monad.State

import Control.Comonad.Cofree

import Data
import Data.Maybe (catMaybes, fromMaybe)

import qualified Text.Show.Pretty as Pr

type MacroSubst = ([(String, Tree)], [(String, [Tree])])

type Pattern = Tree

macroExpand :: Tree -> WithEnv Tree
macroExpand = recurM macroExpand1

recurM :: (Monad m) => (Tree -> m Tree) -> Tree -> m Tree
recurM f (meta :< TreeAtom s) = f (meta :< TreeAtom s)
recurM f (meta :< TreeNode tis) = do
  tis' <- mapM (recurM f) tis
  f (meta :< TreeNode tis')

-- Given a S-expression, check if the expression matches one of the registered
-- notations.
--   (1) If a match (that is, a pair of substitution and "macro template") is found,
--   replace the holes in the template by the substitution, and recursively try to
--   macro-expand the resulting expression.
--   (2) If the S-expression doesn't match with any registered notations, just return
--   the S-expression itself.
macroExpand1 :: Tree -> WithEnv Tree
macroExpand1 t@(i :< _) = do
  nenv <- gets notationEnv
  mMatch <- try (macroMatch t) nenv
  case mMatch of
    Just (subst, _ :< template) -> do
      let t' = applyMacroSubst subst (i :< template)
      macroExpand t'
    Nothing -> return t

-- returns the first "Just"
try :: (Monad m) => (a -> m (Maybe b)) -> [(a, c)] -> m (Maybe (b, c))
try _ [] = return Nothing
try f ((p, q):as) = do
  mx <- f p
  case mx of
    Nothing -> try f as
    Just x -> return $ Just (x, q)

-- `macroMatch` determines the behavior of matching.
macroMatch ::
     Tree -- input tree
  -> Pattern -- registered notation
  -> WithEnv (Maybe MacroSubst) -- {symbols in a pattern} -> {trees}
macroMatch (i :< TreeAtom s1) (_ :< TreeAtom s2)
  -- Trying to match two atoms. There are three case splits here:
  --   (1) If the input `s1` and the pattern `s2` are both reserved, this matching
  --   succeeds iff s1 == s2.
  --   (2) If the input `s1` and the pattern `s2` are both unreserved, this matching
  --   generates a new substitution from `s2` to `s1`. Namely, a unregistered atoms
  --   in a pattern is regarded as a variable to be filled by pattern matching.
  --   (3) The other cases result in failure.
 = do
  renv <- gets reservedEnv
  case (s1 `elem` renv, s2 `elem` renv) of
    (True, True)
      | s1 == s2 -> return $ Just ([], [])
    (False, False) -> return $ Just ([(s2, i :< TreeAtom s1)], [])
    _ -> return Nothing
macroMatch t (_ :< TreeAtom s)
  -- The input is a S-expression, and the pattern is (supposed to be) a variable.
  -- We firstly check that the `s` is in fact a variable, that is, not a reserved
  -- keyword. After that, we generate a new substitution from the variable `s` to the
  -- tree `t`.
 = do
  renv <- gets reservedEnv
  if s `notElem` renv
    then return $ Just ([(s, t)], [])
    else return Nothing
macroMatch (_ :< TreeAtom _) (_ :< _)
  -- The input is an atom, and the pattern is a S-expression, which is not an atom.
  -- An atom can't be matched with a tree, so this case immediately fails.
 = return Nothing
macroMatch (_ :< TreeNode ts1) (_ :< TreeNode ts2)
  -- The input is list of S-expressions, and also the pattern is.
  -- We fistly check that the last element of `ts2` is an atom with a name that
  -- ends by '+'. We regard such a names as a name of multiple S-expressions.
  --
  -- For example, suppose that the input is `(e1 2 3 foo 5)` and the pattern is
  -- `(e1 2 rest+)`. In this case, the `rest+` should be matched to the list [3, foo, 5].
  -- This behavior is indispensable when we realize practical macros.
  -- Note that the [3, foo, 5] is not the same as (3 foo 5). the `[3, foo, 5]` is the
  -- list in the meta-language (namely, Haskell), whereas the `(3 foo 5)` is the list
  -- in the object-language (namely, Neut).
 =
  case last ts2 of
    (_ :< TreeAtom sym)
      | last sym == '+'
      , length ts1 >= length ts2
      -- If the last element is such a '+'-suffixed name, we'll try to generate a substitution
      -- as in the example above. We check that the length of `ts2` is the same or greater
      -- than that of `ts1`, so that we can exclude an improper cases such as
      -- `ts1 == (1 2 3)` and `ts2 == (1 2 3 4 rest+)`. From here, as a running example,
      -- let us take `ts1 == (1 2 3 4 5)` and `ts2 == (pat1 pat2 rest+)`. We take the first
      -- (length ts2 - 1) elements from `ts1`, obtaining `(1 2)`. We also take the
      -- first (length ts2 - 1) elements from `ts2`, obtaining `(pat1 pat2)`.
      -- We then match `(1 2)` and `(pat1 pat2)` in the pairwise way, obtaining some
      -- substitution. As for the last element, we generate a substitution from the
      -- last element of `ts2`, namely `rest+`, to the remaining elements of `ts1`, namely
      -- `[3, 4, 5]`. Finally, we combine these results and return it.
       -> do
        let (xs, rest) = splitAt (length ts2 - 1) ts1
        let ys = take (length ts2 - 1) ts2
        mzs <- sequence <$> zipWithM macroMatch xs ys
        case mzs of
          Nothing -> return Nothing
          Just zs -> do
            let (ss, rests) = unzip zs
            return $ Just (join ss, (sym, rest) : join rests)
    _
      | length ts1 == length ts2
      -- If the last element is not a '+'-suffixed name, the `ts1` and `ts2` must be
      -- strictly matched. So we just try to match them in the pairwise way, and return
      -- the resulting substitutions.
       -> do
        mzs <- sequence <$> zipWithM macroMatch ts1 ts2
        case mzs of
          Nothing -> return Nothing
          Just zs -> do
            let (ss, rests) = unzip zs
            return $ Just (join ss, join rests)
    _ -> return Nothing

-- select :: [Maybe a] -> Maybe [a]
-- select [] = return []
-- select (Just a:xs) = do
--   xs' <- select xs
--   return $ a : xs'
-- select (Nothing:_) = Nothing
-- Using the resulting substitution, replace the variables in a pattern.
-- The first projection of MacroSubst is an "ordinary" substitution, namely just a
-- mapping from a name to a tree. The second projection is a "multiple" substitution,
-- namely a mapping from a name to a list of trees.
applyMacroSubst :: MacroSubst -> Pattern -> Tree
applyMacroSubst (s1, _) (i :< TreeAtom s) =
  fromMaybe (i :< TreeAtom s) (lookup s s1)
applyMacroSubst sub@(_, s2) (i :< TreeNode ts)
  -- When we need to replace the last variable of a list, we check if the variable
  -- is a '+'-suffixed one. If it is, we lookup the list of trees from the
  -- substitution `sub` by the '+'-suffixed name, and concatenate the list of
  -- trees to the end of the list. For example, if `ts == (e1 e2 rest+)`, we lookup
  -- the `sub` by "rest+". Suppose that we found a list `[3 4 5]`.
  -- Then, after applying the substitution to `e1` and `e2` recursively, obtaining
  -- `e1'` and `e2'` respectively, we append the `[3 4 5]` to `(e1' e2')`, obtaining
  -- (e1' e2' 3 4 5).
 =
  case last ts of
    (j :< TreeAtom s)
      | last s == '+'
      , s `elem` map fst s2 -> do
        let ts' = map (applyMacroSubst sub) (take (length ts - 1) ts)
        case lookup s s2 of
          Nothing -> j :< TreeNode (ts' ++ [j :< TreeAtom s])
          Just rest -> i :< TreeNode (ts' ++ rest)
    _ -> do
      let ts' = map (applyMacroSubst sub) ts
      i :< TreeNode ts'

-- The '+'-suffixed name can be occurred only at the end of a list
isSaneNotation :: Pattern -> Bool
isSaneNotation (_ :< TreeAtom s) = last s /= '+'
isSaneNotation (_ :< TreeNode ts) = do
  let b = all isSaneNotation $ init ts
  case last ts of
    _ :< TreeAtom _ -> True
    ts' -> b && isSaneNotation ts'
