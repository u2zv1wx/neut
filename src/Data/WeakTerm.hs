module Data.WeakTerm where

import Data.Basic
import qualified Data.IntMap as IntMap
import Data.LowType
import qualified Data.Set as S
import qualified Data.Text as T

data WeakTerm
  = WeakTermTau
  | WeakTermUpsilon Ident
  | WeakTermPi [WeakIdentPlus] WeakTermPlus
  | WeakTermPiIntro [WeakIdentPlus] WeakTermPlus
  | WeakTermPiElim WeakTermPlus [WeakTermPlus]
  | WeakTermFix WeakIdentPlus [WeakIdentPlus] WeakTermPlus
  | WeakTermAster Int
  | WeakTermConst T.Text
  | WeakTermInt WeakTermPlus Integer
  | WeakTermFloat WeakTermPlus Double
  | WeakTermEnum T.Text
  | WeakTermEnumIntro T.Text
  | WeakTermEnumElim (WeakTermPlus, WeakTermPlus) [(EnumCasePlus, WeakTermPlus)]
  | WeakTermTensor [WeakTermPlus]
  | WeakTermTensorIntro [WeakTermPlus]
  | WeakTermTensorElim [WeakIdentPlus] WeakTermPlus WeakTermPlus
  | WeakTermQuestion WeakTermPlus WeakTermPlus -- e : t (output the type `t` as note)
  | WeakTermDerangement Derangement WeakTermPlus [(WeakTermPlus, DerangementArg, WeakTermPlus)] -- (derangement NUM result-type arg-1 ... arg-n)
  deriving (Show)

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

data WeakStmt
  = WeakStmtDef Hint WeakIdentPlus WeakTermPlus
  | WeakStmtResourceType Hint T.Text WeakTermPlus WeakTermPlus
  deriving (Show)

type Constraint =
  (WeakTermPlus, WeakTermPlus) -- (expected-type, actual-type)

type SuspendedConstraint = (S.Set Int, Constraint)

toVar :: Hint -> Ident -> WeakTermPlus
toVar m x =
  (m, WeakTermUpsilon x)

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
    (_, WeakTermUpsilon x) ->
      S.singleton x
    (_, WeakTermPi xts t) ->
      varWeakTermPlus' xts [t]
    (_, WeakTermPiIntro xts e) ->
      varWeakTermPlus' xts [e]
    (_, WeakTermPiElim e es) -> do
      let xs = varWeakTermPlus e
      let ys = S.unions $ map varWeakTermPlus es
      S.union xs ys
    (_, WeakTermFix (_, x, t) xts e) -> do
      let set1 = varWeakTermPlus t
      let set2 = S.filter (/= x) (varWeakTermPlus' xts [e])
      S.union set1 set2
    (_, WeakTermConst _) ->
      S.empty
    (_, WeakTermAster _) ->
      S.empty
    (_, WeakTermInt t _) ->
      varWeakTermPlus t
    (_, WeakTermFloat t _) ->
      varWeakTermPlus t
    (_, WeakTermEnum _) ->
      S.empty
    (_, WeakTermEnumIntro _) ->
      S.empty
    (_, WeakTermEnumElim (e, t) les) -> do
      let xs = varWeakTermPlus t
      let ys = varWeakTermPlus e
      let zs = S.unions $ map (varWeakTermPlus . snd) les
      S.unions [xs, ys, zs]
    (_, WeakTermTensor ts) ->
      S.unions $ map varWeakTermPlus ts
    (_, WeakTermTensorIntro es) ->
      S.unions $ map varWeakTermPlus es
    (_, WeakTermTensorElim xts e1 e2) -> do
      let xs = varWeakTermPlus e1
      let ys = varWeakTermPlus' xts [e2]
      S.unions [xs, ys]
    (_, WeakTermQuestion e t) -> do
      let set1 = varWeakTermPlus e
      let set2 = varWeakTermPlus t
      S.union set1 set2
    (_, WeakTermDerangement _ t ekts) -> do
      let (es, _, ts) = unzip3 ekts
      S.unions $ varWeakTermPlus t : map varWeakTermPlus (es ++ ts)

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
    (_, WeakTermUpsilon _) ->
      S.empty
    (_, WeakTermPi xts t) ->
      asterWeakTermPlus' xts [t]
    (_, WeakTermPiIntro xts e) ->
      asterWeakTermPlus' xts [e]
    (_, WeakTermPiElim e es) -> do
      let set1 = asterWeakTermPlus e
      let set2 = S.unions $ map asterWeakTermPlus es
      S.union set1 set2
    (_, WeakTermFix (_, _, t) xts e) -> do
      let set1 = asterWeakTermPlus t
      let set2 = asterWeakTermPlus' xts [e]
      S.union set1 set2
    (_, WeakTermAster h) ->
      S.singleton h
    (_, WeakTermConst _) ->
      S.empty
    (_, WeakTermInt t _) ->
      asterWeakTermPlus t
    (_, WeakTermFloat t _) ->
      asterWeakTermPlus t
    (_, WeakTermEnum _) ->
      S.empty
    (_, WeakTermEnumIntro _) ->
      S.empty
    (_, WeakTermEnumElim (e, t) les) -> do
      let set1 = asterWeakTermPlus e
      let set2 = asterWeakTermPlus t
      let set3 = S.unions $ map (\(_, body) -> asterWeakTermPlus body) les
      S.unions [set1, set2, set3]
    (_, WeakTermTensor ts) ->
      S.unions $ map asterWeakTermPlus ts
    (_, WeakTermTensorIntro es) ->
      S.unions $ map asterWeakTermPlus es
    (_, WeakTermTensorElim xts e1 e2) -> do
      let xs = asterWeakTermPlus e1
      let ys = asterWeakTermPlus' xts [e2]
      S.unions [xs, ys]
    (_, WeakTermQuestion e t) -> do
      let set1 = asterWeakTermPlus e
      let set2 = asterWeakTermPlus t
      S.union set1 set2
    (_, WeakTermDerangement _ t ekts) -> do
      let (es, _, ts) = unzip3 ekts
      S.unions $ asterWeakTermPlus t : map asterWeakTermPlus (es ++ ts)

asterWeakTermPlus' :: [WeakIdentPlus] -> [WeakTermPlus] -> S.Set Int
asterWeakTermPlus' binder es =
  case binder of
    [] ->
      S.unions $ map asterWeakTermPlus es
    ((_, _, t) : xts) -> do
      let set1 = asterWeakTermPlus t
      let set2 = asterWeakTermPlus' xts es
      S.union set1 set2

metaOf :: WeakTermPlus -> Hint
metaOf =
  fst

asUpsilon :: WeakTermPlus -> Maybe Ident
asUpsilon term =
  case term of
    (_, WeakTermUpsilon x) ->
      Just x
    _ ->
      Nothing

toText :: WeakTermPlus -> T.Text
toText term =
  case term of
    (_, WeakTermTau) ->
      "tau"
    (_, WeakTermUpsilon x) ->
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
    (_, WeakTermPiIntro xts e) -> do
      let argStr = inParen $ showItems $ map showArg xts
      showCons ["λ", argStr, toText e]
    (_, WeakTermPiElim e es) ->
      case e of
        (_, WeakTermAster _) ->
          "*"
        _ ->
          showCons $ map toText $ e : es
    (_, WeakTermFix (_, x, _) _ _) -> do
      asText x
    -- (_, WeakTermFix (_, x, _) xts e) -> do
    --   let argStr = inParen $ showItems $ map showArg xts
    --   showCons ["fix", showVariable x, argStr, toText e]
    (_, WeakTermConst x) ->
      x
    (_, WeakTermAster _) ->
      "*"
    (_, WeakTermInt _ a) ->
      T.pack $ show a
    (_, WeakTermFloat _ a) ->
      T.pack $ show a
    (_, WeakTermEnum l) ->
      l
    (_, WeakTermEnumIntro v) ->
      v
    (_, WeakTermEnumElim (e, _) mles) -> do
      let (mls, es) = unzip mles
      let les = zip (map snd mls) es
      showCons ["switch", toText e, showItems (map showClause les)]
    (_, WeakTermTensor ts) -> do
      let ts' = map toText ts
      showCons $ "tensor" : ts'
    (_, WeakTermTensorIntro es) -> do
      let es' = map toText es
      showCons $ "tensor-introduction" : es'
    (_, WeakTermTensorElim xts e1 e2) -> do
      showCons ["tensor-elimination", inParen (showTypeArgs xts), toText e1, toText e2]
    (_, WeakTermQuestion e _) ->
      toText e
    (_, WeakTermDerangement i resultType ekts) -> do
      let resultType' = toText resultType
      let (es, _, _) = unzip3 ekts
      let es' = map toText es
      showCons $ "derangement" : T.pack (show i) : resultType' : es'

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
  if T.any (\c -> c `S.member` S.fromList "()") $ asText x
    then "_"
    else asText' x

showClause :: (EnumCase, WeakTermPlus) -> T.Text
showClause (c, e) =
  inParen $ showCase c <> " " <> toText e

showCase :: EnumCase -> T.Text
showCase c =
  case c of
    EnumCaseLabel l ->
      l
    EnumCaseDefault ->
      "default"

showDerangementArgKind :: DerangementArg -> T.Text
showDerangementArgKind k =
  case k of
    DerangementArgLinear ->
      "linear"
    DerangementArgAffine ->
      "affine"

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
