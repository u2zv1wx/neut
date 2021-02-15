module Data.Hint where

import Path

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
    metaLocation :: Loc,
    metaIsReducible :: Bool
  }

-- required to derive the eqality on WeakTerm
instance Eq Hint where
  _ == _ =
    True

instance Show Hint where
  show _ =
    "_"

instance Ord Hint where
  compare _ _ =
    EQ

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
      metaLocation = supLocation m1 m2,
      metaIsReducible = metaIsReducible m1 && metaIsReducible m2
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
      metaLocation = (p, l, c),
      metaIsReducible = True
    }

type PosInfo =
  (Path Abs File, Loc)

getPosInfo :: Hint -> PosInfo
getPosInfo m =
  (metaFileName m, metaLocation m)

showPosInfo :: Path Abs File -> Loc -> String
showPosInfo path (_, l, c) =
  toFilePath path ++ ":" ++ show l ++ ":" ++ show c
