module Data.Basic where

import qualified Data.Set as S
import qualified Data.Text as T
import Path

newtype Ident
  = I (T.Text, Int)
  deriving (Eq, Ord)

instance Show Ident where
  show (I (s, i)) =
    T.unpack s ++ "-" ++ show i

type Phase =
  Int

type Line =
  Int

type Column =
  Int

type Loc =
  (Phase, Line, Column)

data Hint = Hint
  { metaFileName :: Path Abs File,
    metaLocation :: Loc
  }

type PosInfo =
  (Path Abs File, Loc)

instance Show Hint where
  show _ =
    "_"

data EnumCase
  = EnumCaseLabel T.Text
  | EnumCaseInteger Integer
  | EnumCaseDefault
  deriving (Show, Eq, Ord)

type EnumCasePlus =
  (Hint, EnumCase)

asText :: Ident -> T.Text
asText (I (s, _)) =
  s

asText' :: Ident -> T.Text
asText' (I (s, i)) =
  s <> "-" <> T.pack (show i)

asText'' :: Ident -> T.Text
asText'' (I (_, i)) =
  "_" <> T.pack (show i)

asIdent :: T.Text -> Ident
asIdent s =
  I (s, 0)

asInt :: Ident -> Int
asInt (I (_, i)) =
  i

isLinear :: (Eq a, Ord a) => [a] -> Bool
isLinear =
  isLinear' S.empty

isLinear' :: (Eq a, Ord a) => S.Set a -> [a] -> Bool
isLinear' found input =
  case input of
    [] ->
      True
    (x : xs)
      | x `S.member` found ->
        False
      | otherwise ->
        isLinear' (S.insert x found) xs

showHint :: Hint -> String
showHint m = do
  let name = metaFileName m
  let (_, l, c) = metaLocation m
  toFilePath name ++ ":" ++ show l ++ ":" ++ show c

showHint' :: Hint -> String
showHint' m = do
  let name = metaFileName m
  let (ph, l, c) = metaLocation m
  toFilePath name ++ ":" ++ show ph ++ ":" ++ show l ++ ":" ++ show c

supHint :: Hint -> Hint -> Hint
supHint m1 m2 =
  Hint
    { metaFileName = supFileName m1 m2,
      metaLocation = supLocation m1 m2
    }

supFileName :: Hint -> Hint -> Path Abs File
supFileName m1 m2 =
  case metaLocation m1 `compare` metaLocation m2 of
    GT -> metaFileName m1
    _ -> metaFileName m2

supLocation :: Hint -> Hint -> Loc
supLocation m1 m2 =
  case metaLocation m1 `compare` metaLocation m2 of
    GT -> metaLocation m1
    _ -> metaLocation m2

newHint :: Int -> Int -> Int -> Path Abs File -> Hint
newHint p l c path =
  Hint
    { metaFileName = path,
      metaLocation = (p, l, c)
    }

getPosInfo :: Hint -> PosInfo
getPosInfo m =
  (metaFileName m, metaLocation m)

showPosInfo :: Path Abs File -> Loc -> String
showPosInfo path (_, l, c) =
  toFilePath path ++ ":" ++ show l ++ ":" ++ show c
