module Data.Meta where

import Path

type Phase =
  Int

type Line =
  Int

type Column =
  Int

type Loc =
  (Phase, Line, Column)

data Meta
  = Meta
      { metaFileName :: Path Abs File,
        metaLocation :: Loc,
        metaIsReducible :: Bool
      }

-- required to derive the eqality on WeakTerm
instance Eq Meta where
  _ == _ =
    True

instance Show Meta where
  show _ =
    "_"

instance Ord Meta where
  compare _ _ =
    EQ

showMeta :: Meta -> String
showMeta m = do
  let name = metaFileName m
  let (_, l, c) = metaLocation m
  toFilePath name ++ ":" ++ show l ++ ":" ++ show c

showMeta' :: Meta -> String
showMeta' m = do
  let name = metaFileName m
  let (ph, l, c) = metaLocation m
  toFilePath name ++ ":" ++ show ph ++ ":" ++ show l ++ ":" ++ show c

supMeta :: Meta -> Meta -> Meta
supMeta m1 m2 =
  Meta
    { metaFileName = supFileName m1 m2,
      metaLocation = supLocation m1 m2,
      metaIsReducible = metaIsReducible m1 && metaIsReducible m2
    }

supFileName :: Meta -> Meta -> Path Abs File
supFileName m1 m2 =
  case metaLocation m1 `compare` metaLocation m2 of
    GT -> metaFileName m1
    _ -> metaFileName m2

supLocation :: Meta -> Meta -> Loc
supLocation m1 m2 =
  case metaLocation m1 `compare` metaLocation m2 of
    GT -> metaLocation m1
    _ -> metaLocation m2

newMeta :: Int -> Int -> Path Abs File -> Meta
newMeta l c path =
  Meta
    { metaFileName = path,
      metaLocation = (0, l, c),
      metaIsReducible = True
    }

type PosInfo =
  (Path Abs File, Loc)

getPosInfo :: Meta -> PosInfo
getPosInfo m =
  (metaFileName m, metaLocation m)

showPosInfo :: Path Abs File -> Loc -> String
showPosInfo path (_, l, c) =
  toFilePath path ++ ":" ++ show l ++ ":" ++ show c
