module Parse.MacroExpand
  ( macroExpand
  , checkNotation
  ) where

import Control.Monad.Except
import Control.Monad.State

import qualified Data.Set as S

import Data.Basic
import Data.Env
import Data.Maybe (fromMaybe)
import Data.Tree

type MacroSubst = [(String, TreePlus)]

-- {} macroExpand {noSplice, noKeyword}
-- CBV-like macro expansion
macroExpand :: TreePlus -> WithEnv TreePlus
macroExpand t = do
  result <- recurM (macroExpand1 . splice) t
  let info = toInfo "macroExpand.post" result
  assertPM info result $ noSpliceOrKeyword result

macroExpand' :: TreePlus -> WithEnv TreePlus
macroExpand' t = recurM (macroExpand1 . splice) t

noSpliceOrKeyword :: TreePlus -> WithEnv Bool
noSpliceOrKeyword t = do
  let noSplice = hasNoRemSplice t
  noKeyword <- hasNoMatch t
  return $ noSplice && noKeyword

hasNoRemSplice :: TreePlus -> Bool
hasNoRemSplice (_, TreeAtom _) = True
hasNoRemSplice (_, TreeNode ts) = do
  let b1 = all hasNoRemSplice ts
  let b2 = all (isLeft . findSplice) ts
  b1 && b2

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False

-- noRemKeywordというか、noMatchが正解。
hasNoMatch :: TreePlus -> WithEnv Bool
hasNoMatch t = do
  nenv <- gets notationEnv
  mMatch <- try (macroMatch t) nenv
  case mMatch of
    Just _ -> return False
    Nothing -> return True

-- {} recurM {}
recurM :: (Monad m) => (TreePlus -> m TreePlus) -> TreePlus -> m TreePlus
recurM f (m, TreeAtom s) = f (m, TreeAtom s)
recurM f (m, TreeNode ts) = do
  ts' <- mapM (recurM f) ts
  f (m, TreeNode ts')

-- substの結果がkeywordを含んでいることは普通にありうる。
-- {(noSplice)} macroExpand1 {(noSplice, noMatch)}
macroExpand1 :: TreePlus -> WithEnv TreePlus
macroExpand1 t@(i, _) = do
  assertUP (toInfo "macroExpand1.pre" t) $ hasNoRemSplice t
  nenv <- gets notationEnv
  mMatch <- try (macroMatch t) nenv
  case mMatch of
    Just (sub, (_, skel)) -> macroExpand' $ applySubst sub (i, skel)
    Nothing -> return t

type Notation = TreePlus

-- {} macroMatch {}
macroMatch ::
     TreePlus -- input tree
  -> Notation -- registered notation
  -> WithEnv (Maybe MacroSubst) -- {symbols in a pattern} -> {trees}
macroMatch t1@(_, TreeAtom s1) (_, TreeAtom s2) = do
  kenv <- gets keywordEnv
  case s2 `elem` kenv of
    True
      | s1 == s2 -> return $ Just []
      | otherwise -> return Nothing
    False -> return $ Just [(s2, t1)]
macroMatch t1@(_, TreeNode _) (_, TreeAtom s2) = do
  kenv <- gets keywordEnv
  case s2 `elem` kenv of
    True -> return Nothing
    False -> return $ Just [(s2, t1)]
macroMatch (_, TreeAtom _) (_, TreeNode _) = return Nothing
macroMatch (_, TreeNode []) (_, TreeNode []) = return $ Just []
macroMatch (_, TreeNode _) (_, TreeNode []) = return Nothing
macroMatch (_, TreeNode []) (_, TreeNode _) = return Nothing
macroMatch (_, TreeNode ts1) (_, TreeNode ts2)
  | (_, TreeAtom s2) <- last ts2
  , last s2 == '+' -- this ensures that s2 is not a keyword
  , length ts1 >= length ts2 = do
    let (xs, rest) = splitAt (length ts2 - 1) ts1
    let ys = take (length ts2 - 1) ts2
    mzs <- sequence <$> zipWithM macroMatch xs ys
    return $ mzs >>= \zs -> Just $ (s2, toSpliceTree rest) : join zs
  | length ts1 == length ts2 = do
    mzs <- sequence <$> zipWithM macroMatch ts1 ts2
    return $ mzs >>= \zs -> Just $ join zs
  | otherwise = return Nothing

-- {} applySubst {}
applySubst :: MacroSubst -> Notation -> TreePlus
applySubst sub (i, TreeAtom s) = fromMaybe (i, TreeAtom s) (lookup s sub)
applySubst sub (i, TreeNode ts) = (i, TreeNode $ map (applySubst sub) ts)

toSpliceTree :: [TreePlus] -> TreePlus
toSpliceTree ts =
  ( emptyMeta
  , TreeNode [(emptyMeta, TreeAtom "splice"), (emptyMeta, TreeNode ts)])

-- {} checkNotation {}
checkNotation :: Notation -> WithEnv ()
checkNotation t = do
  checkKeywordCondition t
  checkPlusCondition t

-- {} checkKeywordCondition {}
checkKeywordCondition :: Notation -> WithEnv ()
checkKeywordCondition t = do
  kenv <- gets keywordEnv
  if not $ null $ kenv `S.intersection` atomListOf t
    then return ()
    else throwError "A notation must include at least one keyword"

-- {} checkPlusCondition {}
checkPlusCondition :: Notation -> WithEnv ()
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

-- {} splice {noSplice}
splice :: TreePlus -> TreePlus
splice t = do
  let result = splice' t
  let info = toInfo "splice" t
  assertP info result $ hasNoRemSplice result

-- (a b (splice (c (splice (p q)) e)) f) ~> (a b c p q d e)
splice' :: TreePlus -> TreePlus
splice' t@(_, TreeAtom _) = t
splice' (m, TreeNode ts) = do
  let ts' = map splice' ts
  (m, TreeNode $ expandSplice $ map findSplice ts')

-- {} findSplice {}
findSplice :: TreePlus -> Either TreePlus [TreePlus]
findSplice (_, TreeNode [(_, TreeAtom "splice"), (_, TreeNode ts)]) = do
  Right ts
findSplice t = Left t

-- {} expandSplice {}
expandSplice :: [Either TreePlus [TreePlus]] -> [TreePlus]
expandSplice [] = []
expandSplice (Left t:rest) = t : expandSplice rest
expandSplice (Right ts:rest) = ts ++ expandSplice rest

-- {} try {}
-- returns the first "Just"
try :: (Monad m) => (a -> m (Maybe b)) -> [(a, c)] -> m (Maybe (b, c))
try _ [] = return Nothing
try f ((s, t):as) = do
  mx <- f s
  case mx of
    Nothing -> try f as
    Just x -> return $ Just (x, t)
