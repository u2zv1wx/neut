module Data.Size where

import qualified Data.Text as T

type IntSize =
  Int

data FloatSize
  = FloatSize16
  | FloatSize32
  | FloatSize64
  deriving (Eq, Ord, Show)

asFloatSize :: Int -> Maybe FloatSize
asFloatSize size =
  case size of
    16 ->
      Just FloatSize16
    32 ->
      Just FloatSize32
    64 ->
      Just FloatSize64
    _ ->
      Nothing

showIntSize :: IntSize -> T.Text
showIntSize size =
  "i" <> T.pack (show size)

showFloatSize :: FloatSize -> T.Text
showFloatSize size =
  "f" <> T.pack (show $ sizeAsInt size)

sizeAsInt :: FloatSize -> Int
sizeAsInt size =
  case size of
    FloatSize16 ->
      16
    FloatSize32 ->
      32
    FloatSize64 ->
      64
