module Data.WeakTerm where

import Data.EnumCase
import Data.Ident
import qualified Data.IntMap as IntMap
import Data.LowType
import Data.Meta
import qualified Data.Set as S
import Data.Size
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
  | WeakTermArray WeakTermPlus ArrayKind -- array n3 u8 ~= n3 -> u8
  | WeakTermArrayIntro ArrayKind [WeakTermPlus]
  | WeakTermArrayElim ArrayKind [WeakIdentPlus] WeakTermPlus WeakTermPlus
  | WeakTermStruct [ArrayKind]
  | WeakTermStructIntro [(WeakTermPlus, ArrayKind)]
  | WeakTermStructElim [(Meta, Ident, ArrayKind)] WeakTermPlus WeakTermPlus
  | WeakTermQuestion WeakTermPlus WeakTermPlus -- e : t (output the type `t` as note)
  | WeakTermErase [(Meta, T.Text)] WeakTermPlus
  deriving (Show, Eq)

type WeakTermPlus =
  (Meta, WeakTerm)

type SubstWeakTerm =
  IntMap.IntMap WeakTermPlus

type WeakIdentPlus =
  (Meta, Ident, WeakTermPlus)

type WeakTextPlus =
  (Meta, T.Text, WeakTermPlus)

type Def =
  (Meta, WeakIdentPlus, [WeakIdentPlus], WeakTermPlus)

type IdentDef =
  (Ident, Def)

toVar :: Meta -> Ident -> WeakTermPlus
toVar m x =
  (m, WeakTermUpsilon x)

i8 :: Meta -> WeakTermPlus
i8 m =
  (m, WeakTermConst (showIntSize 8))

i64 :: Meta -> WeakTermPlus
i64 m =
  (m, WeakTermConst (showIntSize 64))

data WeakStmt
  = WeakStmtLet Meta WeakIdentPlus WeakTermPlus
  | WeakStmtLetBypass Meta WeakIdentPlus WeakTermPlus
  | WeakStmtConstDecl WeakTextPlus
  deriving (Show)

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
    (_, WeakTermArray dom _) ->
      varWeakTermPlus dom
    (_, WeakTermArrayIntro _ es) ->
      S.unions $ map varWeakTermPlus es
    (_, WeakTermArrayElim _ xts d e) ->
      varWeakTermPlus d `S.union` varWeakTermPlus' xts [e]
    (_, WeakTermStruct {}) ->
      S.empty
    (_, WeakTermStructIntro ets) ->
      S.unions $ map (varWeakTermPlus . fst) ets
    (_, WeakTermStructElim xts d e) -> do
      let xs = map (\(_, x, _) -> x) xts
      let set1 = varWeakTermPlus d
      let set2 = S.filter (`notElem` xs) (varWeakTermPlus e)
      S.union set1 set2
    (_, WeakTermQuestion e t) -> do
      let set1 = varWeakTermPlus e
      let set2 = varWeakTermPlus t
      S.union set1 set2
    (_, WeakTermErase _ e) ->
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
    (_, WeakTermArray dom _) ->
      asterWeakTermPlus dom
    (_, WeakTermArrayIntro _ es) ->
      S.unions $ map asterWeakTermPlus es
    (_, WeakTermArrayElim _ xts d e) -> do
      let set1 = asterWeakTermPlus d
      let set2 = asterWeakTermPlus' xts [e]
      S.union set1 set2
    (_, WeakTermStruct {}) ->
      S.empty
    (_, WeakTermStructIntro ets) ->
      S.unions $ map (asterWeakTermPlus . fst) ets
    (_, WeakTermStructElim _ d e) -> do
      let set1 = asterWeakTermPlus d
      let set2 = asterWeakTermPlus e
      S.union set1 set2
    (_, WeakTermQuestion e t) -> do
      let set1 = asterWeakTermPlus e
      let set2 = asterWeakTermPlus t
      S.union set1 set2
    (_, WeakTermErase _ e) ->
      asterWeakTermPlus e

asterWeakTermPlus' :: [WeakIdentPlus] -> [WeakTermPlus] -> S.Set Int
asterWeakTermPlus' binder es =
  case binder of
    [] ->
      S.unions $ map asterWeakTermPlus es
    ((_, _, t) : xts) -> do
      let set1 = asterWeakTermPlus t
      let set2 = asterWeakTermPlus' xts es
      S.union set1 set2

substWeakTermPlus :: SubstWeakTerm -> WeakTermPlus -> WeakTermPlus
substWeakTermPlus sub term =
  case term of
    (_, WeakTermTau) ->
      term
    (_, WeakTermUpsilon x) ->
      case IntMap.lookup (asInt x) sub of
        Nothing ->
          term
        Just e2@(_, e) ->
          (supMeta (metaOf term) (metaOf e2), e)
    (m, WeakTermPi xts t) -> do
      let (xts', t') = substWeakTermPlus'' sub xts t
      (m, WeakTermPi xts' t')
    (m, WeakTermPiIntro xts body) -> do
      let (xts', body') = substWeakTermPlus'' sub xts body
      (m, WeakTermPiIntro xts' body')
    (m, WeakTermPiElim e es) -> do
      let e' = substWeakTermPlus sub e
      let es' = map (substWeakTermPlus sub) es
      (m, WeakTermPiElim e' es')
    (m, WeakTermFix (mx, x, t) xts e) -> do
      let t' = substWeakTermPlus sub t
      let sub' = IntMap.delete (asInt x) sub
      let (xts', e') = substWeakTermPlus'' sub' xts e
      (m, WeakTermFix (mx, x, t') xts' e')
    (_, WeakTermConst _) ->
      term
    (_, WeakTermAster x) ->
      case IntMap.lookup x sub of
        Nothing ->
          term
        Just e2@(_, e) ->
          (supMeta (metaOf term) (metaOf e2), e)
    (m, WeakTermInt t x) -> do
      let t' = substWeakTermPlus sub t
      (m, WeakTermInt t' x)
    (m, WeakTermFloat t x) -> do
      let t' = substWeakTermPlus sub t
      (m, WeakTermFloat t' x)
    (m, WeakTermEnum x) ->
      (m, WeakTermEnum x)
    (m, WeakTermEnumIntro l) ->
      (m, WeakTermEnumIntro l)
    (m, WeakTermEnumElim (e, t) branchList) -> do
      let t' = substWeakTermPlus sub t
      let e' = substWeakTermPlus sub e
      let (caseList, es) = unzip branchList
      let es' = map (substWeakTermPlus sub) es
      (m, WeakTermEnumElim (e', t') (zip caseList es'))
    (m, WeakTermArray dom k) -> do
      let dom' = substWeakTermPlus sub dom
      (m, WeakTermArray dom' k)
    (m, WeakTermArrayIntro k es) -> do
      let es' = map (substWeakTermPlus sub) es
      (m, WeakTermArrayIntro k es')
    (m, WeakTermArrayElim mk xts v e) -> do
      let v' = substWeakTermPlus sub v
      let (xts', e') = substWeakTermPlus'' sub xts e
      (m, WeakTermArrayElim mk xts' v' e')
    (m, WeakTermStruct ts) ->
      (m, WeakTermStruct ts)
    (m, WeakTermStructIntro ets) -> do
      let (es, ts) = unzip ets
      let es' = map (substWeakTermPlus sub) es
      (m, WeakTermStructIntro $ zip es' ts)
    (m, WeakTermStructElim xts v e) -> do
      let v' = substWeakTermPlus sub v
      let xs = map (\(_, x, _) -> x) xts
      let sub' = foldr IntMap.delete sub (map asInt xs)
      let e' = substWeakTermPlus sub' e
      (m, WeakTermStructElim xts v' e')
    (m, WeakTermQuestion e t) -> do
      let e' = substWeakTermPlus sub e
      let t' = substWeakTermPlus sub t
      (m, WeakTermQuestion e' t')
    (m, WeakTermErase xs e) -> do
      let e' = substWeakTermPlus sub e
      (m, WeakTermErase xs e')

substWeakTermPlus' :: SubstWeakTerm -> [WeakIdentPlus] -> [WeakIdentPlus]
substWeakTermPlus' sub binder =
  case binder of
    [] ->
      []
    ((m, x, t) : xts) -> do
      let sub' = IntMap.delete (asInt x) sub
      let xts' = substWeakTermPlus' sub' xts
      let t' = substWeakTermPlus sub t
      (m, x, t') : xts'

substWeakTermPlus'' ::
  SubstWeakTerm ->
  [WeakIdentPlus] ->
  WeakTermPlus ->
  ([WeakIdentPlus], WeakTermPlus)
substWeakTermPlus'' sub binder e =
  case binder of
    [] ->
      ([], substWeakTermPlus sub e)
    ((m, x, t) : xts) -> do
      let sub' = IntMap.delete (asInt x) sub
      let (xts', e') = substWeakTermPlus'' sub' xts e
      let t' = substWeakTermPlus sub t
      ((m, x, t') : xts', e')

metaOf :: WeakTermPlus -> Meta
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
    (_, WeakTermFix (_, x, _) xts e) -> do
      let argStr = inParen $ showItems $ map showArg xts
      showCons ["fix", showVariable x, argStr, toText e]
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
    (_, WeakTermArray dom k) ->
      showCons ["array", toText dom, showArrayKind k]
    (_, WeakTermArrayIntro _ es) ->
      showCons $ "array-introduction" : map toText es
    (_, WeakTermArrayElim _ xts e1 e2) -> do
      let argStr = inParen $ showItems $ map showArg xts
      showCons ["array-elimination", argStr, toText e1, toText e2]
    (_, WeakTermStruct ks) ->
      showCons $ "struct" : map showArrayKind ks
    (_, WeakTermStructIntro ets) ->
      showCons $ "struct-introduction" : map (toText . fst) ets
    (_, WeakTermStructElim xts e1 e2) -> do
      let argStr = inParen $ showItems $ map (\(_, x, _) -> asText x) xts
      showCons ["struct-elimination", argStr, toText e1, toText e2]
    (_, WeakTermQuestion e _) ->
      toText e
    (_, WeakTermErase _ e) ->
      toText e

inParen :: T.Text -> T.Text
inParen s =
  "(" <> s <> ")"

showArg :: (Meta, Ident, WeakTermPlus) -> T.Text
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
    else asText x

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

showArrayKind :: ArrayKind -> T.Text
showArrayKind arrayKind =
  case arrayKind of
    ArrayKindInt size ->
      showIntSize size
    ArrayKindFloat size ->
      showFloatSize size
    ArrayKindVoidPtr ->
      "void*"

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
