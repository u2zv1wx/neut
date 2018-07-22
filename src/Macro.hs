module Macro
  ( macroExpand
  , loadMacroDef
  ) where

import           Control.Monad
import           Control.Monad.State

import           Data
import           Data.Maybe          (fromMaybe)

import qualified Text.Show.Pretty    as Pr

type Subst = ([(String, Tree)], [(String, [Tree])])

type Pattern = Tree

-- ASTのリストを受け取って、前から読んでいく。予約語の定義が見つかったら、その情報で環境を
-- 更新し、その定義をリストから除去して残りを読む。マクロの定義が見つかったら、やはりその情報で
-- 環境を更新し、定義をリストから除去して残りを読む。最終的に、ASTのリストから、予約後の定義と
-- マクロの定義を除いたものを返す。
loadMacroDef :: [Tree] -> WithEnv [Tree]
loadMacroDef [] = return []
loadMacroDef (Node (Atom "reserve":[Atom s]):as) = do
  modify (\e -> e {reservedEnv = s : reservedEnv e})
  loadMacroDef as
loadMacroDef (Node (Atom "notation":[from, to]):as) = do
  modify (\e -> e {notationEnv = (from, to) : notationEnv e})
  loadMacroDef as
loadMacroDef (a:as) = do
  as' <- loadMacroDef as
  return $ a : as'

-- - fromの中に出てくる変数でtoの中に出現する変数が尽くされることを確認する。
-- - rest変数が、すべてリストの末尾に出現していることを確認する。
sanityCheck :: (Pattern, Pattern) -> Either String ()
sanityCheck = undefined

-- "body+" のように、末尾が '+' で終わるようなシンボルを「1個以上の式の繰り返し」を
-- 表現するための記号として採用する。これはBNF記法からの類推である。
isRest :: String -> Bool
isRest s = last s == '+'

-- 予約語のリストと入力の木とパターンを受け取り、予約語の情報を使いながら木とパターンを
-- マッチさせていく。マッチに成功した時には、substitution, つまりシンボルと木への対応関係が返る。
macroMatch :: [String] -> Tree -> Pattern -> Maybe Subst
macroMatch rs (Atom s1) (Atom s2) =
  case (s1 `elem` rs, s2 `elem` rs) of
    (True, True)
      | s1 == s2 -> return ([], [])
    (False, False) -> return ([(s2, Atom s1)], [])
    _ -> Nothing
macroMatch rs t (Atom s) =
  if s `elem` rs
    then Nothing
    else return ([(s, t)], [])
macroMatch rs (Atom s) t = Nothing
macroMatch rs (Node ts1) (Node ts2) =
  case last ts2 of
    Atom sym
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
applySubst :: Subst -> Tree -> Tree
applySubst (s1, _) (Atom s) = fromMaybe (Atom s) (lookup s s1)
applySubst sub@(_, s2) (Node ts) =
  case last ts of
    Atom s
      | isRest s && s `elem` map fst s2 -> do
        let tsButLast' = map (applySubst sub) (take (length ts - 1) ts)
        case lookup s s2 of
          Nothing   -> undefined
          Just rest -> Node $ tsButLast' ++ rest
    _ -> do
      let ts' = map (applySubst sub) ts
      Node ts'

-- 関数fをリストの第1要素に対して作用させ、最初にJustが得られたときの要素と第2要素のペアを返す。
-- Justが得られなかったときにはNothingを返す。
try :: (a -> Maybe b) -> [(a, c)] -> Maybe (b, c)
try f [] = Nothing
try f ((p, q):as) =
  case f p of
    Nothing -> try f as
    Just x  -> Just (x, q)

macroExpand1 :: Tree -> WithEnv Tree
macroExpand1 t = do
  env <- get
  let nenv = notationEnv env
  let renv = reservedEnv env
  case try (macroMatch renv t) nenv of
    Just (subst, template) -> do
      let t' = applySubst subst template
      macroExpand t'
    Nothing -> return t

-- これをtermについてinductiveにやる必要がある。
-- macroの展開が起こったか否かをフラグで管理するべき？
macroExpand :: Tree -> WithEnv Tree
macroExpand = recurM macroExpand1
