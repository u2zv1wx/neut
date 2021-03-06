module Data.WeakTerm where

import Data.Basic
import qualified Data.IntMap as IntMap
import Data.LowType
import Data.Maybe (catMaybes, maybeToList)
import qualified Data.PQueue.Min as Q
import qualified Data.Set as S
import qualified Data.Text as T
import Path

data WeakTerm
  = WeakTermTau
  | WeakTermVar VarKind Ident
  | WeakTermPi [WeakIdentPlus] WeakTermPlus
  | WeakTermPiIntro Opacity (LamKind WeakIdentPlus) [WeakIdentPlus] WeakTermPlus
  | WeakTermPiElim WeakTermPlus [WeakTermPlus]
  | WeakTermAster Int
  | WeakTermConst T.Text
  | WeakTermInt WeakTermPlus Integer
  | WeakTermFloat WeakTermPlus Double
  | WeakTermEnum (Path Abs File) T.Text
  | WeakTermEnumIntro (Path Abs File) T.Text
  | WeakTermEnumElim (WeakTermPlus, WeakTermPlus) [(EnumCasePlus, WeakTermPlus)]
  | WeakTermQuestion WeakTermPlus WeakTermPlus -- e : t (output the type `t` as note)
  | WeakTermDerangement Derangement [WeakTermPlus] -- (derangement kind arg-1 ... arg-n)
  | WeakTermCase
      WeakTermPlus -- result type
      (Maybe WeakTermPlus) -- noetic subject (this is for `case-noetic`)
      (WeakTermPlus, WeakTermPlus) -- (pattern-matched value, its type)
      [(WeakPattern, WeakTermPlus)]
  | WeakTermIgnore WeakTermPlus
  deriving (Show)

type WeakPattern =
  (Hint, Ident, [WeakIdentPlus])

type WeakTermPlus =
  (Hint, WeakTerm)

type SubstWeakTerm =
  IntMap.IntMap WeakTermPlus

type WeakIdentPlus =
  (Hint, Ident, WeakTermPlus)

type WeakTextPlus =
  (Hint, T.Text, WeakTermPlus)

type Def =
  (Hint, WeakIdentPlus, [WeakIdentPlus], WeakTermPlus)

type IdentDef =
  (Ident, Def)

type WeakStmtPlus =
  (Path Abs File, [WeakStmt])

data WeakStmt
  = WeakStmtDef Hint Ident WeakTermPlus WeakTermPlus
  | WeakStmtUse T.Text
  | WeakStmtUnuse T.Text
  | WeakStmtDefinePrefix T.Text T.Text
  | WeakStmtRemovePrefix T.Text T.Text
  deriving (Show)

type Constraint =
  (WeakTermPlus, WeakTermPlus) -- (expected-type, actual-type)

type MetaVarSet =
  S.Set Int

data ConstraintKind
  = ConstraintKindDelta Constraint
  | ConstraintKindOther
  deriving (Show)

newtype SuspendedConstraint
  = SuspendedConstraint (MetaVarSet, ConstraintKind, (Constraint, Constraint))

instance Eq SuspendedConstraint where
  (SuspendedConstraint (_, kind1, _)) == (SuspendedConstraint (_, kind2, _)) =
    kindToInt kind1 == kindToInt kind2

instance Ord SuspendedConstraint where
  (SuspendedConstraint (_, kind1, _)) `compare` (SuspendedConstraint (_, kind2, _)) =
    kindToInt kind1 `compare` kindToInt kind2

type SuspendedConstraintQueue = Q.MinQueue SuspendedConstraint

toVar :: Hint -> Ident -> WeakTermPlus
toVar m x =
  (m, WeakTermVar VarKindLocal x)

kindToInt :: ConstraintKind -> Int
kindToInt k =
  case k of
    ConstraintKindDelta {} ->
      0
    ConstraintKindOther {} ->
      1

i8 :: Hint -> WeakTermPlus
i8 m =
  (m, WeakTermConst (showIntSize 8))

i64 :: Hint -> WeakTermPlus
i64 m =
  (m, WeakTermConst (showIntSize 64))

varWeakTermPlus :: WeakTermPlus -> S.Set Ident
varWeakTermPlus term =
  case term of
    (_, WeakTermTau) ->
      S.empty
    (_, WeakTermVar opacity x) ->
      case opacity of
        VarKindLocal ->
          S.singleton x
        _ ->
          S.empty
    (_, WeakTermPi xts t) ->
      varWeakTermPlus' xts [t]
    (_, WeakTermPiIntro _ k xts e) ->
      varWeakTermPlus' (catMaybes [fromLamKind k] ++ xts) [e]
    (_, WeakTermPiElim e es) -> do
      let xs = varWeakTermPlus e
      let ys = S.unions $ map varWeakTermPlus es
      S.union xs ys
    (_, WeakTermConst _) ->
      S.empty
    (_, WeakTermAster _) ->
      S.empty
    (_, WeakTermInt t _) ->
      varWeakTermPlus t
    (_, WeakTermFloat t _) ->
      varWeakTermPlus t
    (_, WeakTermEnum _ _) ->
      S.empty
    (_, WeakTermEnumIntro _ _) ->
      S.empty
    (_, WeakTermEnumElim (e, t) les) -> do
      let xs = varWeakTermPlus t
      let ys = varWeakTermPlus e
      let zs = S.unions $ map (varWeakTermPlus . snd) les
      S.unions [xs, ys, zs]
    (_, WeakTermQuestion e t) -> do
      let set1 = varWeakTermPlus e
      let set2 = varWeakTermPlus t
      S.union set1 set2
    (_, WeakTermDerangement _ es) ->
      S.unions $ map varWeakTermPlus es
    (_, WeakTermCase resultType mSubject (e, t) patList) -> do
      let xs1 = varWeakTermPlus resultType
      let xs2 = S.unions $ map varWeakTermPlus $ maybeToList mSubject
      let xs3 = varWeakTermPlus e
      let xs4 = varWeakTermPlus t
      let xs5 = S.unions $ map (\((_, _, xts), body) -> varWeakTermPlus' xts [body]) patList
      S.unions [xs1, xs2, xs3, xs4, xs5]
    (_, WeakTermIgnore e) ->
      varWeakTermPlus e

varWeakTermPlus' :: [WeakIdentPlus] -> [WeakTermPlus] -> S.Set Ident
varWeakTermPlus' binder es =
  case binder of
    [] ->
      S.unions $ map varWeakTermPlus es
    ((_, x, t) : xts) -> do
      let hs1 = varWeakTermPlus t
      let hs2 = varWeakTermPlus' xts es
      S.union hs1 $ S.filter (/= x) hs2

asterWeakTermPlus :: WeakTermPlus -> S.Set Int
asterWeakTermPlus term =
  case term of
    (_, WeakTermTau) ->
      S.empty
    (_, WeakTermVar _ _) ->
      S.empty
    (_, WeakTermPi xts t) ->
      asterWeakTermPlus' xts t
    (_, WeakTermPiIntro _ _ xts e) ->
      asterWeakTermPlus' xts e
    (_, WeakTermPiElim e es) ->
      S.unions $ map asterWeakTermPlus $ e : es
    (_, WeakTermAster h) ->
      S.singleton h
    (_, WeakTermConst _) ->
      S.empty
    (_, WeakTermInt t _) ->
      asterWeakTermPlus t
    (_, WeakTermFloat t _) ->
      asterWeakTermPlus t
    (_, WeakTermEnum _ _) ->
      S.empty
    (_, WeakTermEnumIntro _ _) ->
      S.empty
    (_, WeakTermEnumElim (e, t) les) -> do
      let set1 = asterWeakTermPlus e
      let set2 = asterWeakTermPlus t
      let set3 = S.unions $ map (\(_, body) -> asterWeakTermPlus body) les
      S.unions [set1, set2, set3]
    (_, WeakTermQuestion e t) -> do
      let set1 = asterWeakTermPlus e
      let set2 = asterWeakTermPlus t
      S.union set1 set2
    (_, WeakTermDerangement _ es) ->
      S.unions $ map asterWeakTermPlus es
    (_, WeakTermCase resultType mSubject (e, t) patList) -> do
      let xs1 = asterWeakTermPlus resultType
      let xs2 = S.unions $ map asterWeakTermPlus $ maybeToList mSubject
      let xs3 = asterWeakTermPlus e
      let xs4 = asterWeakTermPlus t
      let xs5 = S.unions $ map (\((_, _, xts), body) -> asterWeakTermPlus' xts body) patList
      S.unions [xs1, xs2, xs3, xs4, xs5]
    (_, WeakTermIgnore e) ->
      asterWeakTermPlus e

asterWeakTermPlus' :: [WeakIdentPlus] -> WeakTermPlus -> S.Set Int
asterWeakTermPlus' binder e =
  case binder of
    [] ->
      asterWeakTermPlus e
    ((_, _, t) : xts) -> do
      let set1 = asterWeakTermPlus t
      let set2 = asterWeakTermPlus' xts e
      S.union set1 set2

metaOf :: WeakTermPlus -> Hint
metaOf =
  fst

asVar :: WeakTermPlus -> Maybe Ident
asVar term =
  case term of
    (_, WeakTermVar _ x) ->
      Just x
    _ ->
      Nothing

toText :: WeakTermPlus -> T.Text
toText term =
  case term of
    (_, WeakTermTau) ->
      "tau"
    (_, WeakTermVar _ x) ->
      showVariable x
    (_, WeakTermPi xts cod)
      | [(_, I ("internal.sigma-tau", _), _), (_, _, (_, WeakTermPi yts _))] <- xts ->
        case splitLast yts of
          Nothing ->
            "(product)"
          Just (zts, (_, _, t)) ->
            showCons ["∑", inParen $ showTypeArgs zts, toText t]
      | otherwise ->
        showCons ["Π", inParen $ showTypeArgs xts, toText cod]
    (_, WeakTermPiIntro opacity kind xts e) -> do
      case kind of
        LamKindFix (_, x, _) -> do
          let argStr = inParen $ showItems $ map showArg xts
          if isOpaque opacity
            then showCons ["fix-irreducible", showVariable x, argStr, toText e]
            else showCons ["fix", showVariable x, argStr, toText e]
        LamKindCons _ _ -> do
          let argStr = inParen $ showItems $ map showArg xts
          if isTransparent opacity
            then showCons ["λ", argStr, toText e]
            else showCons ["λ-irreducible", argStr, toText e]
        -- "<cons>"
        _ -> do
          let argStr = inParen $ showItems $ map showArg xts
          if isTransparent opacity
            then showCons ["λ", argStr, toText e]
            else showCons ["λ-irreducible", argStr, toText e]
    (_, WeakTermPiElim e es) ->
      case e of
        -- (_, WeakTermAster _) ->
        --   "*"
        _ ->
          showCons $ map toText $ e : es
    (_, WeakTermConst x) ->
      x
    (_, WeakTermAster i) ->
      "?M" <> T.pack (show i)
    (_, WeakTermInt _ a) ->
      T.pack $ show a
    (_, WeakTermFloat _ a) ->
      T.pack $ show a
    (_, WeakTermEnum path l) ->
      l <> "@" <> T.pack (toFilePath path)
    (_, WeakTermEnumIntro _ v) ->
      v
    (_, WeakTermEnumElim (e, _) mles) -> do
      let (mls, es) = unzip mles
      let les = zip (map snd mls) es
      showCons ["switch", toText e, showItems (map showClause les)]
    (_, WeakTermQuestion e _) ->
      toText e
    (_, WeakTermDerangement i es) -> do
      let es' = map toText es
      showCons $ "derangement" : T.pack (show i) : es'
    (_, WeakTermCase _ mSubject (e, _) caseClause) -> do
      case mSubject of
        Nothing -> do
          showCons $ "case" : toText e : map showCaseClause caseClause
        Just _ -> do
          showCons $ "case-noetic" : toText e : map showCaseClause caseClause
    (_, WeakTermIgnore e) ->
      showCons ["ignore", toText e]

inParen :: T.Text -> T.Text
inParen s =
  "(" <> s <> ")"

showArg :: (Hint, Ident, WeakTermPlus) -> T.Text
showArg (_, x, t) =
  inParen $ showVariable x <> " " <> toText t

showTypeArgs :: [WeakIdentPlus] -> T.Text
showTypeArgs args =
  case args of
    [] ->
      T.empty
    [(_, x, t)] ->
      inParen $ showVariable x <> " " <> toText t
    (_, x, t) : xts -> do
      let s1 = inParen $ showVariable x <> " " <> toText t
      let s2 = showTypeArgs xts
      s1 <> " " <> s2

showVariable :: Ident -> T.Text
showVariable x =
  asText x

showCaseClause :: (WeakPattern, WeakTermPlus) -> T.Text
showCaseClause (pat, e) =
  inParen $ showPattern pat <> " " <> toText e

showPattern :: (Hint, Ident, [WeakIdentPlus]) -> T.Text
showPattern (_, f, xts) = do
  case xts of
    [] ->
      inParen $ asText f
    _ -> do
      let xs = map (\(_, x, _) -> x) xts
      inParen $ asText f <> " " <> T.intercalate " " (map showVariable xs)

showClause :: (EnumCase, WeakTermPlus) -> T.Text
showClause (c, e) =
  inParen $ showCase c <> " " <> toText e

showCase :: EnumCase -> T.Text
showCase c =
  case c of
    EnumCaseLabel _ l ->
      l
    EnumCaseDefault ->
      "default"
    EnumCaseInt i ->
      T.pack (show i)

showItems :: [T.Text] -> T.Text
showItems =
  T.intercalate " "

showCons :: [T.Text] -> T.Text
showCons =
  inParen . T.intercalate " "

splitLast :: [a] -> Maybe ([a], a)
splitLast xs =
  if null xs
    then Nothing
    else Just (init xs, last xs)
