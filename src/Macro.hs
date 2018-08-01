module Macro
  ( macroExpand
  ) where

import           Control.Monad
import           Control.Monad.State

import           Data
import           Data.Maybe          (fromMaybe)

import qualified Text.Show.Pretty    as Pr

type Subst = ([(String, MTree)], [(String, [MTree])])

type Pattern = Tree

sanityCheck :: (Pattern, Pattern) -> Either String ()
sanityCheck = undefined

-- "body+" のように、末尾が '+' で終わるようなシンボルを「1個以上の式の繰り返し」を
-- 表現するための記号として採用する。これはBNF記法からの類推である。
isRest :: String -> Bool
isRest s = last s == '+'

-- 予約語のリストと入力の木とパターンを受け取り、予約語の情報を使いながら木とパターンを
-- マッチさせていく。マッチに成功した時には、substitution, つまりシンボルと木への対応関係が返る。
macroMatch :: [String] -> MTree -> MTree -> Maybe Subst
macroMatch rs (Atom s1, i) (Atom s2, _) =
  case (s1 `elem` rs, s2 `elem` rs) of
    (True, True)
      | s1 == s2 -> return ([], [])
    (False, False) -> return ([(s2, (Atom s1, i))], [])
    _ -> Nothing
macroMatch rs t (Atom s, _) =
  if s `elem` rs
    then Nothing
    else return ([(s, t)], [])
macroMatch rs (Atom s, i) (t, _) = Nothing
macroMatch rs (Node ts1, i) (Node ts2, _) =
  case last ts2 of
    (Atom sym, _)
      | isRest sym && length ts1 >= length ts2 -> do
        let (xs, rest) = splitAt (length ts2 - 1) ts1
        let ys = take (length ts2 - 1) ts2
        (ss, rests) <- unzip <$> zipWithM (macroMatch rs) xs ys
        return (join ss, (sym, rest) : join rests)
    _
      | length ts1 == length ts2 -> do
        (ss, rests) <- unzip <$> zipWithM (macroMatch rs) ts1 ts2
        return (join ss, join rests)
    _ -> Nothing

-- substitutionをtreeに対して作用させる。
applySubst :: Subst -> MTree -> MTree
applySubst (s1, _) (Atom s, i) = fromMaybe (Atom s, i) (lookup s s1)
applySubst sub@(_, s2) (Node ts, i) =
  case last ts of
    (Atom s, j)
      | isRest s && s `elem` map fst s2 -> do
        let tsButLast' = map (applySubst sub) (take (length ts - 1) ts)
        case lookup s s2 of
          Nothing   -> undefined
          Just rest -> (Node $ tsButLast' ++ rest, j)
    (_, j) -> do
      let ts' = map (applySubst sub) ts
      (Node ts', j)

-- 関数fをリストの第1要素に対して作用させ、最初にJustが得られたときの要素と第2要素のペアを返す。
-- Justが得られなかったときにはNothingを返す。
try :: (a -> Maybe b) -> [(a, c)] -> Maybe (b, c)
try f [] = Nothing
try f ((p, q):as) =
  case f p of
    Nothing -> try f as
    Just x  -> Just (x, q)

macroExpand1 :: MTree -> WithEnv MTree
macroExpand1 t@(_, i) = do
  env <- get
  let nenv = notationEnv env
  let renv = reservedEnv env
  case try (macroMatch renv t) nenv of
    Just (subst, template) -> do
      let t' = applySubst subst (fst template, i)
      macroExpand t'
    Nothing -> return t

-- これをtermについてinductiveにやる必要がある。
-- macroの展開が起こったか否かをフラグで管理するべき？
macroExpand :: MTree -> WithEnv MTree
macroExpand = recurM macroExpand1
