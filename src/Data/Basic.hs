module Data.Basic where

import qualified Data.Text as T
import Path

newtype Ident
  = I (T.Text, Int)
  deriving (Eq, Ord)

instance Show Ident where
  show (I (s, i)) =
    T.unpack s ++ "-" ++ show i

type Line =
  Int

type Column =
  Int

type Loc =
  (Line, Column)

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
  | EnumCaseInt Int
  | EnumCaseDefault
  deriving (Show, Eq, Ord)

type EnumCasePlus =
  (Hint, EnumCase)

data Opacity
  = OpacityOpaque
  | OpacityTranslucent
  | OpacityTransparent
  deriving (Show)

data VarKind
  = VarKindLocal
  | VarKindGlobalOpaque
  | VarKindGlobalTransparent
  deriving (Show)

data LamKind a
  = LamKindNormal
  | LamKindCons T.Text T.Text
  | LamKindFix a
  | LamKindResourceHandler
  deriving (Show)

type IsReducible =
  Bool

isOpaque :: Opacity -> Bool
isOpaque o =
  case o of
    OpacityOpaque ->
      True
    _ ->
      False

isTransparent :: Opacity -> Bool
isTransparent o =
  case o of
    OpacityTransparent ->
      True
    _ ->
      False

fromLamKind :: LamKind a -> Maybe a
fromLamKind k =
  case k of
    LamKindFix x ->
      Just x
    _ ->
      Nothing

lamKindWeakEq :: LamKind a -> LamKind a -> Bool
lamKindWeakEq k1 k2 =
  case (k1, k2) of
    (LamKindNormal, LamKindNormal) ->
      True
    (LamKindCons t11 t12, LamKindCons t21 t22) ->
      t11 == t21 && t12 == t22
    _ ->
      False

asText :: Ident -> T.Text
asText (I (s, _)) =
  s

{-# INLINE asText' #-}
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

showHint :: Hint -> String
showHint m = do
  let name = metaFileName m
  let (l, c) = metaLocation m
  toFilePath name ++ ":" ++ show l ++ ":" ++ show c

newHint :: Int -> Int -> Path Abs File -> Hint
newHint l c path =
  Hint
    { metaFileName = path,
      metaLocation = (l, c)
    }

getPosInfo :: Hint -> PosInfo
getPosInfo m =
  (metaFileName m, metaLocation m)

showPosInfo :: Path Abs File -> Loc -> String
showPosInfo path (l, c) =
  toFilePath path ++ ":" ++ show l ++ ":" ++ show c
