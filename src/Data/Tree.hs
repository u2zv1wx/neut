module Data.Tree where

import Data.Basic
import qualified Data.Text as T

data Tree
  = TreeLeaf T.Text
  | TreeNode [TreePlus]
  deriving (Show)

data Doc
  = DocEmpty
  | DocText T.Text Doc
  | DocLine Int Doc

type TreePlus =
  (Hint, Tree)

docEmpty :: Doc
docEmpty =
  DocEmpty

docText :: T.Text -> Doc
docText s =
  DocText s DocEmpty

docLine :: Doc
docLine =
  DocLine 0 DocEmpty

docNest :: Int -> Doc -> Doc
docNest i d =
  case d of
    DocEmpty ->
      DocEmpty
    DocText s d' ->
      DocText s (docNest i d')
    DocLine j d' ->
      DocLine (i + j) (docNest i d')

docConcat :: Doc -> Doc -> Doc
docConcat d1 d2 =
  case d1 of
    DocEmpty ->
      d2
    DocText s d1' ->
      DocText s (docConcat d1' d2)
    DocLine i d1' ->
      DocLine i (docConcat d1' d2)

(+++) :: Doc -> Doc -> Doc
d1 +++ d2 = docConcat d1 d2

layoutDoc :: Doc -> T.Text
layoutDoc d =
  case d of
    DocEmpty ->
      ""
    DocText s d' ->
      s <> layoutDoc d'
    DocLine i d' ->
      "\n" <> T.replicate i " " <> layoutDoc d'

docParen :: Doc -> Doc
docParen d =
  docText "(" +++ docNest 1 d +++ docText ")"

docTree :: TreePlus -> Doc
docTree tree =
  case tree of
    (_, TreeLeaf x) ->
      docText x
    (_, TreeNode ts) -> do
      docParen (docTreeList ts)

docTreeList :: [TreePlus] -> Doc
docTreeList treeList =
  case treeList of
    [ (_, TreeLeaf "Π"),
      ( _,
        TreeNode
          [ (_, TreeNode [(_, TreeLeaf sig1), (_, TreeLeaf "tau")]),
            (_, TreeNode [(_, TreeLeaf _), (_, TreeNode [(_, TreeLeaf "Π"), (_, TreeNode xts), (_, TreeLeaf sig1')])])
            ]
        ),
      (_, TreeLeaf sig1'')
      ]
        | T.isPrefixOf "sig;" sig1,
          sig1 == sig1',
          sig1 == sig1'',
          length xts > 0,
          Just t <- treeSnd (last xts) ->
          docText "Σ" +++ docLine +++ docMap docArg (init xts) +++ docLine +++ docTree t
    [ (_, TreeLeaf "Π"),
      ( _,
        TreeNode
          [ (_, TreeNode [(_, TreeLeaf prod1), (_, TreeLeaf "tau")]),
            (_, TreeNode [(_, TreeLeaf _), (_, TreeNode [(_, TreeLeaf "Π"), (_, TreeNode xts), (_, TreeLeaf prod1')])])
            ]
        ),
      (_, TreeLeaf prod1'')
      ]
        | T.isPrefixOf "prod;" prod1,
          prod1 == prod1',
          prod1 == prod1'',
          Just ts <- mapM treeSnd xts ->
          docText "product " +++ docTreeList ts
    [ (_, TreeLeaf "λ"),
      ( _,
        TreeNode
          [ (_, TreeNode [(_, TreeLeaf sig1), (_, TreeLeaf "tau")]),
            (_, TreeNode [(_, TreeLeaf sig2), (_, TreeNode [(_, TreeLeaf "Π"), (_, TreeNode _), (_, TreeLeaf sig1')])])
            ]
        ),
      (_, TreeNode ((_, TreeLeaf sig2') : args))
      ]
        | T.isPrefixOf "sig;" sig1,
          sig1 == sig1',
          sig2 == sig2' ->
          docText "tuple " +++ docTreeList args
    [t@(_, TreeLeaf headAtom), xts, body]
      | headAtom `elem` ["λ", "Π"] ->
        docTree t +++ docLine +++ docMapOnTree docArg xts +++ docLine +++ docTree body
    [t@(_, TreeLeaf headAtom), self, xts, body]
      | headAtom `elem` ["fix", "fix-irreducible"] ->
        docTree t +++ docText " " +++ docTree self +++ docLine +++ docMapOnTree docArg xts +++ docLine +++ docTree body
    (t@(_, TreeLeaf "switch") : item : clauseList) ->
      docTree t +++ docText " " +++ docTree item +++ docLine +++ docMap docClause clauseList -- docClauseList clauseList
    (t@(_, TreeLeaf "case") : item : clauseList) ->
      docTree t +++ docText " " +++ docTree item +++ docLine +++ docMap docClause clauseList -- docClauseList clauseList
    [(_, TreeNode [(_, TreeLeaf "λ"), (_, TreeNode [(_, TreeNode [(_, TreeLeaf witVar1), t])]), (_, TreeLeaf witVar2)]), body]
      | witVar1 == witVar2,
        T.isPrefixOf "wit;" witVar1 ->
        docText "witness " +++ docLine +++ docTree t +++ docLine +++ docTree body
    [] ->
      docEmpty
    [t] ->
      docTree t
    t : ts ->
      if all isLeaf ts
        then docTree t +++ docText " " +++ docTreeList ts -- all-leafなときはこれでいいけど,そうじゃないときはnewlineがほしいかな。
        else docPiElim treeList

docPiElim :: [TreePlus] -> Doc
docPiElim tree =
  case tree of
    [] ->
      docEmpty
    [t] ->
      docTree t
    t : ts ->
      docTree t +++ docLine +++ docPiElim ts

docArg :: TreePlus -> Doc
docArg tree =
  case tree of
    (_, TreeNode [t1, t2]) ->
      if isLeaf t2
        then docParen (docTree t1 +++ docText " " +++ docTree t2)
        else docParen (docTree t1 +++ docLine +++ docTree t2)
    _ ->
      docTree tree

docMap :: (TreePlus -> Doc) -> [TreePlus] -> Doc
docMap f treeList =
  case treeList of
    [] ->
      docEmpty
    [t] ->
      f t
    t : ts ->
      f t +++ docLine +++ docMap f ts

docMapOnTree :: (TreePlus -> Doc) -> TreePlus -> Doc
docMapOnTree f tree =
  case tree of
    (_, TreeLeaf x) ->
      docParen (docText x)
    (_, TreeNode xts) ->
      docParen (docMap f xts)

docClause :: TreePlus -> Doc
docClause tree =
  case tree of
    (_, TreeNode [t1, t2]) ->
      docParen (docTree t1 +++ docLine +++ docTree t2)
    _ ->
      docTree tree

showTree :: TreePlus -> T.Text
showTree =
  layoutDoc . docTree

showAsSExp :: TreePlus -> T.Text
showAsSExp tree =
  case tree of
    (_, TreeLeaf x) ->
      x
    (_, TreeNode [(_, TreeLeaf "quote"), t]) ->
      "`" <> showAsSExp t
    (_, TreeNode [(_, TreeLeaf "unquote"), t]) ->
      "," <> showAsSExp t
    (_, TreeNode ts) ->
      "(" <> T.intercalate " " (map showAsSExp ts) <> ")"

isLeaf :: TreePlus -> Bool
isLeaf tree =
  case tree of
    (_, TreeLeaf _) ->
      True
    _ ->
      False

treeSnd :: TreePlus -> Maybe TreePlus
treeSnd tree =
  case tree of
    (_, TreeNode [_, t2]) ->
      Just t2
    _ ->
      Nothing
