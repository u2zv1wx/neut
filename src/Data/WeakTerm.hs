module Data.WeakTerm where

import Data.Basic
import qualified Data.IntMap as IntMap
import Data.LowType
import qualified Data.Set as S
import qualified Data.Text as T

data WeakTerm
  = WeakTermTau
  | WeakTermUpsilon Ident
  | WeakTermPi (Maybe T.Text) [WeakIdentPlus] WeakTermPlus
  | WeakTermPiIntro
      (Maybe (Ident, T.Text, [WeakIdentPlus]))
      [WeakIdentPlus]
      WeakTermPlus
  | WeakTermPiElim WeakTermPlus [WeakTermPlus]
  | WeakTermIter WeakIdentPlus [WeakIdentPlus] WeakTermPlus
  | WeakTermHole Ident
  | WeakTermConst T.Text
  | WeakTermBoxElim Ident
  | WeakTermInt WeakTermPlus Integer
  | WeakTermFloat WeakTermPlus Double
  | WeakTermEnum T.Text
  | WeakTermEnumIntro T.Text
  | WeakTermEnumElim (WeakTermPlus, WeakTermPlus) [(EnumCasePlus, WeakTermPlus)]
  | WeakTermArray WeakTermPlus ArrayKind -- array n3 u8 ~= n3 -> u8
  | WeakTermArrayIntro ArrayKind [WeakTermPlus]
  | WeakTermArrayElim
      ArrayKind
      [WeakIdentPlus] -- [(x1, return t1), ..., (xn, return tn)] with xi : ti
      WeakTermPlus
      WeakTermPlus
  | WeakTermStruct [ArrayKind] -- e.g. (struct u8 u8 f16 f32 u64)
  | WeakTermStructIntro [(WeakTermPlus, ArrayKind)]
  | WeakTermStructElim [(Meta, Ident, ArrayKind)] WeakTermPlus WeakTermPlus
  | WeakTermCase
      (Maybe Ident)
      WeakTermPlus
      [(((Meta, Ident), [WeakIdentPlus]), WeakTermPlus)]
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

weakTermPiIntro :: [WeakIdentPlus] -> WeakTermPlus -> WeakTerm
weakTermPiIntro =
  WeakTermPiIntro Nothing

toVar :: Meta -> Ident -> WeakTermPlus
toVar m x =
  (m, WeakTermUpsilon x)

i8 :: Meta -> WeakTermPlus
i8 m =
  (m, WeakTermConst (showIntSize 8))

i64 :: Meta -> WeakTermPlus
i64 m =
  (m, WeakTermConst (showIntSize 64))

type Rule = -- inference rule
  ( Meta, -- location of the name
    T.Text, -- the name of the rule
    Meta, -- location of the rule
    [WeakIdentPlus], -- the antecedents of the inference rule (e.g. [(x, A), (xs, list A)])
    WeakTermPlus -- the consequent of the inference rule
  )

type Connective =
  ( Meta, -- location of the connective
    T.Text, -- the name of the connective (e.g. nat, list)
    [WeakIdentPlus], -- parameter of the connective (e.g. the `A` in `list A`)
    [Rule] -- list of introduction rule when inductive / list of elimination rule when coinductive
  )

data WeakStmt
  = WeakStmtLet Meta WeakIdentPlus WeakTermPlus
  | WeakStmtLetWT Meta WeakIdentPlus WeakTermPlus
  | WeakStmtConstDecl WeakTextPlus
  | WeakStmtVerify Meta WeakTermPlus
  | WeakStmtImplicit Ident [Int]
  deriving (Show)

weakTermPi :: [WeakIdentPlus] -> WeakTermPlus -> WeakTerm
weakTermPi =
  WeakTermPi Nothing

varWeakTermPlus :: WeakTermPlus -> S.Set Ident
varWeakTermPlus term =
  case term of
    (_, WeakTermTau) ->
      S.empty
    (_, WeakTermUpsilon x) ->
      S.singleton x
    (_, WeakTermPi _ xts t) ->
      varWeakTermPlus' xts [t]
    (_, WeakTermPiIntro _ xts e) ->
      varWeakTermPlus' xts [e]
    (_, WeakTermPiElim e es) -> do
      let xs = varWeakTermPlus e
      let ys = S.unions $ map varWeakTermPlus es
      S.union xs ys
    (_, WeakTermIter (_, x, t) xts e) -> do
      let set1 = varWeakTermPlus t
      let set2 = S.filter (/= x) (varWeakTermPlus' xts [e])
      S.union set1 set2
    (_, WeakTermConst _) ->
      S.empty
    (_, WeakTermBoxElim _) ->
      S.empty
    (_, WeakTermHole _) ->
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
    (_, WeakTermCase _ e cxes) -> do
      let xs = varWeakTermPlus e
      let ys = S.unions $ map (\((_, xts), body) -> varWeakTermPlus' xts [body]) cxes
      S.union xs ys
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

holeWeakTermPlus :: WeakTermPlus -> S.Set Ident
holeWeakTermPlus term =
  case term of
    (_, WeakTermTau) ->
      S.empty
    (_, WeakTermUpsilon _) ->
      S.empty
    (_, WeakTermPi _ xts t) ->
      holeWeakTermPlus' xts [t]
    (_, WeakTermPiIntro _ xts e) ->
      holeWeakTermPlus' xts [e]
    (_, WeakTermPiElim e es) -> do
      let set1 = holeWeakTermPlus e
      let set2 = S.unions $ map holeWeakTermPlus es
      S.union set1 set2
    (_, WeakTermIter (_, _, t) xts e) -> do
      let set1 = holeWeakTermPlus t
      let set2 = holeWeakTermPlus' xts [e]
      S.union set1 set2
    (_, WeakTermHole h) ->
      S.singleton h
    (_, WeakTermConst _) ->
      S.empty
    (_, WeakTermBoxElim _) ->
      S.empty
    (_, WeakTermInt t _) ->
      holeWeakTermPlus t
    (_, WeakTermFloat t _) ->
      holeWeakTermPlus t
    (_, WeakTermEnum _) ->
      S.empty
    (_, WeakTermEnumIntro _) ->
      S.empty
    (_, WeakTermEnumElim (e, t) les) -> do
      let set1 = holeWeakTermPlus e
      let set2 = holeWeakTermPlus t
      let set3 = S.unions $ map (\(_, body) -> holeWeakTermPlus body) les
      S.unions [set1, set2, set3]
    (_, WeakTermArray dom _) ->
      holeWeakTermPlus dom
    (_, WeakTermArrayIntro _ es) ->
      S.unions $ map holeWeakTermPlus es
    (_, WeakTermArrayElim _ xts d e) -> do
      let set1 = holeWeakTermPlus d
      let set2 = holeWeakTermPlus' xts [e]
      S.union set1 set2
    (_, WeakTermStruct {}) ->
      S.empty
    (_, WeakTermStructIntro ets) ->
      S.unions $ map (holeWeakTermPlus . fst) ets
    (_, WeakTermStructElim _ d e) -> do
      let set1 = holeWeakTermPlus d
      let set2 = holeWeakTermPlus e
      S.union set1 set2
    (_, WeakTermCase _ e cxes) -> do
      let set1 = holeWeakTermPlus e
      let set2 = S.unions $ map (\((_, xts), body) -> holeWeakTermPlus' xts [body]) cxes
      S.union set1 set2
    (_, WeakTermQuestion e t) -> do
      let set1 = holeWeakTermPlus e
      let set2 = holeWeakTermPlus t
      S.union set1 set2
    (_, WeakTermErase _ e) ->
      holeWeakTermPlus e

holeWeakTermPlus' :: [WeakIdentPlus] -> [WeakTermPlus] -> S.Set Ident
holeWeakTermPlus' binder es =
  case binder of
    [] ->
      S.unions $ map holeWeakTermPlus es
    ((_, _, t) : xts) -> do
      let set1 = holeWeakTermPlus t
      let set2 = holeWeakTermPlus' xts es
      S.union set1 set2

substWeakTermPlus :: SubstWeakTerm -> WeakTermPlus -> WeakTermPlus
substWeakTermPlus sub term =
  case term of
    tau@(_, WeakTermTau) ->
      tau
    e1@(_, WeakTermUpsilon x) ->
      case IntMap.lookup (asInt x) sub of
        Nothing -> e1
        Just e2@(_, e) -> (supMeta (metaOf e1) (metaOf e2), e)
    (m, WeakTermPi mName xts t) -> do
      let (xts', t') = substWeakTermPlus'' sub xts t
      (m, WeakTermPi mName xts' t')
    (m, WeakTermPiIntro info xts body) -> do
      let info' = fmap2 (substWeakTermPlus' sub) info
      let (xts', body') = substWeakTermPlus'' sub xts body
      (m, WeakTermPiIntro info' xts' body')
    (m, WeakTermPiElim e es) -> do
      let e' = substWeakTermPlus sub e
      let es' = map (substWeakTermPlus sub) es
      (m, WeakTermPiElim e' es')
    (m, WeakTermIter (mx, x, t) xts e) -> do
      let t' = substWeakTermPlus sub t
      let sub' = IntMap.delete (asInt x) sub
      let (xts', e') = substWeakTermPlus'' sub' xts e
      (m, WeakTermIter (mx, x, t') xts' e')
    (_, WeakTermConst _) ->
      term
    (_, WeakTermBoxElim _) ->
      term
    e1@(_, WeakTermHole x) ->
      case IntMap.lookup (asInt x) sub of
        Nothing -> e1
        Just e2@(_, e) -> (supMeta (metaOf e1) (metaOf e2), e)
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
      let sub' = deleteKeys sub (map asInt xs)
      let e' = substWeakTermPlus sub' e
      (m, WeakTermStructElim xts v' e')
    (m, WeakTermCase indName e cxtes) -> do
      let e' = substWeakTermPlus sub e
      let cxtes' =
            flip map cxtes $ \((c, xts), body) -> do
              let (xts', body') = substWeakTermPlus'' sub xts body
              ((c, xts'), body')
      (m, WeakTermCase indName e' cxtes')
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
      asText' x
    (_, WeakTermPi Nothing xts cod) ->
      case extractSigmaArg term of
        Just yts ->
          case splitLast yts of
            Just (zts, (_, _, t))
              | isDependent zts t ->
                showCons ["Σ", inParen $ showTypeArgs zts t, toText t]
              | otherwise -> do
                let (_, _, ts) = unzip3 zts
                showCons $ "product" : map toText (ts ++ [t])
            Nothing -> "(product)"
        Nothing
          | isDependent xts cod ->
            showCons ["Π", inParen $ showTypeArgs xts cod, toText cod]
          | otherwise -> do
            let (_, _, ts) = unzip3 xts
            showCons ["arrow", showCons $ map toText ts, toText cod]
    (_, WeakTermPi (Just _) _ cod) ->
      toText cod
    (_, WeakTermPiIntro Nothing xts e) -> do
      let argStr = inParen $ showItems $ map showArg xts
      showCons ["λ", argStr, toText e]
    (_, WeakTermPiIntro (Just (_, name, _)) _ _) ->
      "<#" <> name <> "-" <> "internal" <> "#>"
    (_, WeakTermPiElim e es) ->
      showCons $ map toText $ e : es
    (_, WeakTermIter (_, x, _) xts e) -> do
      let argStr = inParen $ showItems $ map showArg xts
      showCons ["μ", asText' x, argStr, toText e]
    (_, WeakTermConst x) ->
      x
    (_, WeakTermBoxElim x) ->
      asText x
    (_, WeakTermHole (I (_, i))) ->
      "?M" <> T.pack (show i)
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
      showCons ["case", toText e, showItems (map showClause les)]
    (_, WeakTermArray dom k) ->
      showCons ["array", toText dom, showArrayKind k]
    (_, WeakTermArrayIntro _ es) ->
      showArray $ map toText es
    (_, WeakTermArrayElim _ xts e1 e2) -> do
      let argStr = inParen $ showItems $ map showArg xts
      showCons ["array-elimination", argStr, toText e1, toText e2]
    (_, WeakTermStruct ks) ->
      showCons $ "struct" : map showArrayKind ks
    (_, WeakTermStructIntro ets) ->
      showStruct $ map (toText . fst) ets
    (_, WeakTermStructElim xts e1 e2) -> do
      let argStr = inParen $ showItems $ map (\(_, x, _) -> asText x) xts
      showCons ["struct-elimination", argStr, toText e1, toText e2]
    (_, WeakTermCase _ e cxtes) ->
      showCons
        ( "case"
            : toText e
            : flip
              map
              cxtes
              ( \((c, xts), body) -> do
                  let xs = map (\(_, x, _) -> asText x) xts
                  showCons [showCons (asText (snd c) : xs), toText body]
              )
        )
    (_, WeakTermQuestion e _) ->
      toText e
    (_, WeakTermErase _ e) ->
      toText e

inParen :: T.Text -> T.Text
inParen s =
  "(" <> s <> ")"

inAngle :: T.Text -> T.Text
inAngle s =
  "<" <> s <> ">"

inBrace :: T.Text -> T.Text
inBrace s =
  "{" <> s <> "}"

inBracket :: T.Text -> T.Text
inBracket s =
  "[" <> s <> "]"

showArg :: (Meta, Ident, WeakTermPlus) -> T.Text
showArg (_, x, t) =
  inParen $ asText x <> " " <> toText t

showTypeArgs :: [WeakIdentPlus] -> WeakTermPlus -> T.Text
showTypeArgs args cod =
  case args of
    [] ->
      T.empty
    [(_, x, t)]
      | x `S.member` varWeakTermPlus cod ->
        inParen $ asText x <> " " <> toText t
      | otherwise ->
        inParen $ "_" <> " " <> toText t
    (_, x, t) : xts
      | x `S.member` varWeakTermPlus' xts [cod] -> do
        let s1 = inParen $ asText x <> " " <> toText t
        let s2 = showTypeArgs xts cod
        s1 <> " " <> s2
      | otherwise -> do
        let s1 = inParen $ "_" <> " " <> toText t
        let s2 = showTypeArgs xts cod
        s1 <> " " <> s2

isDependent :: [WeakIdentPlus] -> WeakTermPlus -> Bool
isDependent binder cod =
  case binder of
    [] ->
      False
    (_, x, _) : xts
      | x `S.member` varWeakTermPlus' xts [cod] ->
        True
      | otherwise ->
        isDependent xts cod

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
      T.pack $ "i" ++ show size
    ArrayKindFloat size ->
      T.pack $ "f" ++ show (sizeAsInt size)
    ArrayKindVoidPtr ->
      "void*"

showItems :: [T.Text] -> T.Text
showItems =
  T.intercalate " "

showCons :: [T.Text] -> T.Text
showCons =
  inParen . T.intercalate " "

showTuple :: [T.Text] -> T.Text
showTuple =
  inAngle . T.intercalate " "

showArray :: [T.Text] -> T.Text
showArray =
  inBracket . T.intercalate " "

showStruct :: [T.Text] -> T.Text
showStruct =
  inBrace . T.intercalate " "

extractSigmaArg :: WeakTermPlus -> Maybe [WeakIdentPlus]
extractSigmaArg term =
  case term of
    (_, WeakTermPi _ [(_, z, (_, WeakTermTau)), (_, _, (_, WeakTermPi _ xts (_, WeakTermUpsilon z')))] (_, WeakTermUpsilon z''))
      | z == z',
        z == z'' ->
        return xts
    _ -> Nothing

splitLast :: [a] -> Maybe ([a], a)
splitLast input =
  case input of
    [] ->
      Nothing
    [x] ->
      return ([], x)
    (x : xs) -> do
      (xs', z) <- splitLast xs
      return (x : xs', z)
