{-# LANGUAGE OverloadedStrings #-}

module Data.WeakTerm where

import qualified Data.HashMap.Strict as Map
import qualified Data.Set as S
import qualified Data.Text as T

import Data.Basic

data WeakTerm
  = WeakTermTau
  | WeakTermUpsilon Identifier
  | WeakTermPi (Maybe T.Text) [IdentifierPlus] WeakTermPlus
  | WeakTermPiIntro [IdentifierPlus] WeakTermPlus
  | WeakTermPiIntroPlus (T.Text, [IdentifierPlus]) [IdentifierPlus] WeakTermPlus
  | WeakTermPiElim WeakTermPlus [WeakTermPlus]
  | WeakTermIter IdentifierPlus [IdentifierPlus] WeakTermPlus
  | WeakTermZeta Identifier
  | WeakTermConst T.Text
  | WeakTermInt WeakTermPlus Integer
  | WeakTermFloat WeakTermPlus Double
  | WeakTermEnum EnumType
  | WeakTermEnumIntro EnumValue
  | WeakTermEnumElim (WeakTermPlus, WeakTermPlus) [(WeakCasePlus, WeakTermPlus)]
  | WeakTermArray WeakTermPlus ArrayKind -- array n3 u8 ~= n3 -> u8
  | WeakTermArrayIntro ArrayKind [WeakTermPlus]
  | WeakTermArrayElim
      ArrayKind
      [IdentifierPlus] -- [(x1, return t1), ..., (xn, return tn)] with xi : ti
      WeakTermPlus
      WeakTermPlus
  | WeakTermStruct [ArrayKind] -- e.g. (struct u8 u8 f16 f32 u64)
  | WeakTermStructIntro [(WeakTermPlus, ArrayKind)]
  | WeakTermStructElim [(Meta, Identifier, ArrayKind)] WeakTermPlus WeakTermPlus
  | WeakTermCase
      T.Text
      WeakTermPlus
      [(((Meta, T.Text), [IdentifierPlus]), WeakTermPlus)]
  | WeakTermQuestion WeakTermPlus WeakTermPlus -- e : t (output the type `t` as note)
  | WeakTermErase [(Meta, T.Text)] WeakTermPlus
  deriving (Show, Eq)

type WeakTermPlus = (Meta, WeakTerm)

data WeakCase
  = WeakCaseIntS IntSize Integer
  | WeakCaseIntU IntSize Integer
  | WeakCaseInt WeakTermPlus Integer
  | WeakCaseLabel T.Text
  | WeakCaseDefault
  deriving (Show, Eq)

type WeakCasePlus = (Meta, WeakCase)

-- type SubstWeakTerm = [(Identifier, WeakTermPlus)]
-- type SubstWeakTerm = IntMap.IntMap WeakTermPlus
type SubstWeakTerm = Map.HashMap (Either Int T.Text) WeakTermPlus

type IdentifierPlus = (Meta, Identifier, WeakTermPlus)

type TextPlus = (Meta, T.Text, WeakTermPlus)

type Def = (Meta, IdentifierPlus, [IdentifierPlus], WeakTermPlus)

-- type IdentDef = (Identifier, Def)
type IdentDef = (T.Text, Def)

type Rule -- inference rule
   = ( Meta -- location of the name
     -- , Identifier -- the name of the rule
     , T.Text -- the name of the rule
     , Meta -- location of the rule
     , [IdentifierPlus] -- the antecedents of the inference rule (e.g. [(x, A), (xs, list A)])
     , WeakTermPlus -- the consequent of the inference rule
      )

type Connective
   = ( Meta -- location of the connective
     -- , Identifier -- the name of the connective (e.g. nat, list)
     , T.Text -- the name of the connective (e.g. nat, list)
     , [IdentifierPlus] -- parameter of the connective (e.g. the `A` in `list A`)
     , [Rule] -- list of introduction rule when inductive / list of elimination rule when coinductive
      )

data QuasiStmt
  = QuasiStmtLet Meta TextPlus WeakTermPlus
  -- special case of `let` in which the `e` in `let x := e` is known to be well-typed
  | QuasiStmtLetWT Meta TextPlus WeakTermPlus
  -- mutually recursive definition (n >= 0)
  --   (definition
  --     ((f1 A1) (ARGS-1) e1)
  --     ...
  --     ((fn An) (ARGS-n) en))
  | QuasiStmtDef [(T.Text, Def)]
  | QuasiStmtVerify Meta WeakTermPlus
  | QuasiStmtImplicit Meta T.Text [Int]
  | QuasiStmtEnum Meta T.Text [(T.Text, Int)]
  | QuasiStmtConstDecl Meta TextPlus
  | QuasiStmtLetInductive Int Meta TextPlus WeakTermPlus
  | QuasiStmtLetInductiveIntro Meta TextPlus WeakTermPlus [T.Text]
  | QuasiStmtUse T.Text
  | QuasiStmtUnuse T.Text
  deriving (Show)

data WeakStmt
  = WeakStmtReturn WeakTermPlus
  | WeakStmtLet Meta TextPlus WeakTermPlus WeakStmt
  | WeakStmtLetWT Meta TextPlus WeakTermPlus WeakStmt
  | WeakStmtVerify Meta WeakTermPlus WeakStmt
  | WeakStmtImplicit Meta T.Text [Int] WeakStmt
  | WeakStmtConstDecl Meta TextPlus WeakStmt
  deriving (Show)

weakTermPi :: [IdentifierPlus] -> WeakTermPlus -> WeakTerm
weakTermPi = WeakTermPi Nothing

varWeakTermPlus :: WeakTermPlus -> S.Set Identifier
varWeakTermPlus (_, WeakTermTau) = S.empty
varWeakTermPlus (_, WeakTermUpsilon x) = S.singleton x
varWeakTermPlus (_, WeakTermPi _ xts t) = varWeakTermPlus' xts [t]
varWeakTermPlus (_, WeakTermPiIntro xts e) = varWeakTermPlus' xts [e]
varWeakTermPlus (_, WeakTermPiIntroPlus _ xts e) = varWeakTermPlus' xts [e]
varWeakTermPlus (_, WeakTermPiElim e es) = do
  let xs = varWeakTermPlus e
  let ys = S.unions $ map varWeakTermPlus es
  S.union xs ys
varWeakTermPlus (_, WeakTermIter (_, x, t) xts e) = do
  let set1 = varWeakTermPlus t
  let set2 = S.filter (/= x) (varWeakTermPlus' xts [e])
  S.union set1 set2
varWeakTermPlus (_, WeakTermConst _) = S.empty
varWeakTermPlus (_, WeakTermZeta _) = S.empty
varWeakTermPlus (_, WeakTermInt t _) = varWeakTermPlus t
varWeakTermPlus (_, WeakTermFloat t _) = varWeakTermPlus t
varWeakTermPlus (_, WeakTermEnum _) = S.empty
varWeakTermPlus (_, WeakTermEnumIntro _) = S.empty
varWeakTermPlus (_, WeakTermEnumElim (e, t) les) = do
  let xs = varWeakTermPlus t
  let ys = varWeakTermPlus e
  let zs = S.unions $ map (varWeakTermPlus . snd) les
  S.unions [xs, ys, zs]
varWeakTermPlus (_, WeakTermArray dom _) = varWeakTermPlus dom
varWeakTermPlus (_, WeakTermArrayIntro _ es) = S.unions $ map varWeakTermPlus es
varWeakTermPlus (_, WeakTermArrayElim _ xts d e) =
  varWeakTermPlus d `S.union` varWeakTermPlus' xts [e]
varWeakTermPlus (_, WeakTermStruct {}) = S.empty
varWeakTermPlus (_, WeakTermStructIntro ets) =
  S.unions $ map (varWeakTermPlus . fst) ets
varWeakTermPlus (_, WeakTermStructElim xts d e) = do
  let xs = map (\(_, x, _) -> x) xts
  let set1 = varWeakTermPlus d
  let set2 = S.filter (`notElem` xs) (varWeakTermPlus e)
  S.union set1 set2
varWeakTermPlus (_, WeakTermCase _ e cxes) = do
  let xs = varWeakTermPlus e
  let ys =
        S.unions $ map (\((_, xts), body) -> varWeakTermPlus' xts [body]) cxes
  S.union xs ys
varWeakTermPlus (_, WeakTermQuestion e t) = do
  let set1 = varWeakTermPlus e
  let set2 = varWeakTermPlus t
  S.union set1 set2
varWeakTermPlus (_, WeakTermErase _ e) = varWeakTermPlus e

varWeakTermPlus' :: [IdentifierPlus] -> [WeakTermPlus] -> S.Set Identifier
varWeakTermPlus' [] es = S.unions $ map varWeakTermPlus es
varWeakTermPlus' ((_, x, t):xts) es = do
  let hs1 = varWeakTermPlus t
  let hs2 = varWeakTermPlus' xts es
  S.union hs1 $ S.filter (/= x) hs2

holeWeakTermPlus :: WeakTermPlus -> S.Set Identifier
holeWeakTermPlus (_, WeakTermTau) = S.empty
holeWeakTermPlus (_, WeakTermUpsilon _) = S.empty
holeWeakTermPlus (_, WeakTermPi _ xts t) = holeWeakTermPlus' xts [t]
holeWeakTermPlus (_, WeakTermPiIntro xts e) = holeWeakTermPlus' xts [e]
holeWeakTermPlus (_, WeakTermPiIntroPlus {}) = S.empty
holeWeakTermPlus (_, WeakTermPiElim e es) = do
  let set1 = holeWeakTermPlus e
  let set2 = S.unions $ map holeWeakTermPlus es
  S.union set1 set2
holeWeakTermPlus (_, WeakTermIter (_, _, t) xts e) = do
  let set1 = holeWeakTermPlus t
  let set2 = holeWeakTermPlus' xts [e]
  S.union set1 set2
holeWeakTermPlus (_, WeakTermZeta h) = S.singleton h
holeWeakTermPlus (_, WeakTermConst _) = S.empty
holeWeakTermPlus (_, WeakTermInt t _) = holeWeakTermPlus t
holeWeakTermPlus (_, WeakTermFloat t _) = holeWeakTermPlus t
holeWeakTermPlus (_, WeakTermEnum _) = S.empty
holeWeakTermPlus (_, WeakTermEnumIntro _) = S.empty
holeWeakTermPlus (_, WeakTermEnumElim (e, t) les) = do
  let set1 = holeWeakTermPlus e
  let set2 = holeWeakTermPlus t
  let set3 = S.unions $ map (\(_, body) -> holeWeakTermPlus body) les
  S.unions [set1, set2, set3]
holeWeakTermPlus (_, WeakTermArray dom _) = holeWeakTermPlus dom
holeWeakTermPlus (_, WeakTermArrayIntro _ es) =
  S.unions $ map holeWeakTermPlus es
holeWeakTermPlus (_, WeakTermArrayElim _ xts d e) = do
  let set1 = holeWeakTermPlus d
  let set2 = holeWeakTermPlus' xts [e]
  S.union set1 set2
holeWeakTermPlus (_, WeakTermStruct {}) = S.empty
holeWeakTermPlus (_, WeakTermStructIntro ets) =
  S.unions $ map (holeWeakTermPlus . fst) ets
holeWeakTermPlus (_, WeakTermStructElim _ d e) = do
  let set1 = holeWeakTermPlus d
  let set2 = holeWeakTermPlus e
  S.union set1 set2
holeWeakTermPlus (_, WeakTermCase _ e cxes) = do
  let set1 = holeWeakTermPlus e
  let set2 =
        S.unions $ map (\((_, xts), body) -> holeWeakTermPlus' xts [body]) cxes
  S.union set1 set2
holeWeakTermPlus (_, WeakTermQuestion e t) = do
  let set1 = holeWeakTermPlus e
  let set2 = holeWeakTermPlus t
  S.union set1 set2
holeWeakTermPlus (_, WeakTermErase _ e) = holeWeakTermPlus e

holeWeakTermPlus' :: [IdentifierPlus] -> [WeakTermPlus] -> S.Set Identifier
holeWeakTermPlus' [] es = S.unions $ map holeWeakTermPlus es
holeWeakTermPlus' ((_, _, t):xts) es = do
  let set1 = holeWeakTermPlus t
  let set2 = holeWeakTermPlus' xts es
  S.union set1 set2

constWeakTermPlus :: WeakTermPlus -> S.Set T.Text
constWeakTermPlus (_, WeakTermTau) = S.empty
constWeakTermPlus (_, WeakTermUpsilon _) = S.empty
constWeakTermPlus (_, WeakTermPi _ xts t) = constWeakTermPlus' xts [t]
constWeakTermPlus (_, WeakTermPiIntro xts e) = constWeakTermPlus' xts [e]
constWeakTermPlus (_, WeakTermPiIntroPlus _ xts e) = constWeakTermPlus' xts [e]
constWeakTermPlus (_, WeakTermPiElim e es) = do
  let xs = constWeakTermPlus e
  let ys = S.unions $ map constWeakTermPlus es
  S.union xs ys
constWeakTermPlus (_, WeakTermIter (_, _, t) xts e) = do
  let set1 = constWeakTermPlus t
  let set2 = constWeakTermPlus' xts [e]
  S.union set1 set2
constWeakTermPlus (_, WeakTermConst x) = S.singleton x
constWeakTermPlus (_, WeakTermZeta _) = S.empty
constWeakTermPlus (_, WeakTermInt t _) = constWeakTermPlus t
constWeakTermPlus (_, WeakTermFloat t _) = constWeakTermPlus t
constWeakTermPlus (_, WeakTermEnum _) = S.empty
constWeakTermPlus (_, WeakTermEnumIntro _) = S.empty
constWeakTermPlus (_, WeakTermEnumElim (e, t) les) = do
  let xs = constWeakTermPlus t
  let ys = constWeakTermPlus e
  let zs = S.unions $ map (constWeakTermPlus . snd) les
  S.unions [xs, ys, zs]
constWeakTermPlus (_, WeakTermArray dom _) = constWeakTermPlus dom
constWeakTermPlus (_, WeakTermArrayIntro _ es) =
  S.unions $ map constWeakTermPlus es
constWeakTermPlus (_, WeakTermArrayElim _ xts d e) =
  constWeakTermPlus d `S.union` constWeakTermPlus' xts [e]
constWeakTermPlus (_, WeakTermStruct {}) = S.empty
constWeakTermPlus (_, WeakTermStructIntro ets) =
  S.unions $ map (constWeakTermPlus . fst) ets
constWeakTermPlus (_, WeakTermStructElim _ d e) = do
  let set1 = constWeakTermPlus d
  let set2 = constWeakTermPlus e
  S.union set1 set2
constWeakTermPlus (_, WeakTermCase _ e cxes) = do
  let xs = constWeakTermPlus e
  let ys =
        S.unions $ map (\((_, xts), body) -> constWeakTermPlus' xts [body]) cxes
  S.union xs ys
constWeakTermPlus (_, WeakTermQuestion e t) = do
  let set1 = constWeakTermPlus e
  let set2 = constWeakTermPlus t
  S.union set1 set2
constWeakTermPlus (_, WeakTermErase _ e) = constWeakTermPlus e

constWeakTermPlus' :: [IdentifierPlus] -> [WeakTermPlus] -> S.Set T.Text
constWeakTermPlus' [] es = S.unions $ map constWeakTermPlus es
constWeakTermPlus' ((_, _, t):xts) es = do
  let hs1 = constWeakTermPlus t
  let hs2 = constWeakTermPlus' xts es
  S.union hs1 hs2

substWeakTermPlus :: SubstWeakTerm -> WeakTermPlus -> WeakTermPlus
substWeakTermPlus _ tau@(_, WeakTermTau) = tau
substWeakTermPlus sub e1@(_, WeakTermUpsilon x) = do
  case Map.lookup (Left $ asInt x) sub of
    Nothing -> e1
    Just e2@(_, e) -> (supMeta (metaOf e1) (metaOf e2), e)
substWeakTermPlus sub (m, WeakTermPi mName xts t) = do
  let (xts', t') = substWeakTermPlus'' sub xts t
  (m, WeakTermPi mName xts' t')
substWeakTermPlus sub (m, WeakTermPiIntro xts body) = do
  let (xts', body') = substWeakTermPlus'' sub xts body
  (m, WeakTermPiIntro xts' body')
substWeakTermPlus sub (m, WeakTermPiIntroPlus (name, args) xts body) = do
  let args' = substWeakTermPlus' sub args
  let (xts', body') = substWeakTermPlus'' sub xts body
  (m, WeakTermPiIntroPlus (name, args') xts' body')
substWeakTermPlus sub (m, WeakTermPiElim e es) = do
  let e' = substWeakTermPlus sub e
  let es' = map (substWeakTermPlus sub) es
  (m, WeakTermPiElim e' es')
substWeakTermPlus sub (m, WeakTermIter (mx, x, t) xts e) = do
  let t' = substWeakTermPlus sub t
  -- let sub' = filter (\(k, _) -> k /= x) sub
  let sub' = Map.delete (Left $ asInt x) sub
  let (xts', e') = substWeakTermPlus'' sub' xts e
  (m, WeakTermIter (mx, x, t') xts' e')
substWeakTermPlus sub e@(_, WeakTermConst x) = do
  case Map.lookup (Right x) sub of
    Nothing -> e
    Just e2 -> (supMeta (metaOf e) (metaOf e2), snd e2)
  -- e
substWeakTermPlus sub e1@(_, WeakTermZeta x) = do
  case Map.lookup (Left $ asInt x) sub of
    Nothing -> e1
    Just e2@(_, e) -> (supMeta (metaOf e1) (metaOf e2), e)
substWeakTermPlus sub (m, WeakTermInt t x) = do
  let t' = substWeakTermPlus sub t
  (m, WeakTermInt t' x)
substWeakTermPlus sub (m, WeakTermFloat t x) = do
  let t' = substWeakTermPlus sub t
  (m, WeakTermFloat t' x)
substWeakTermPlus _ (m, WeakTermEnum x) = do
  (m, WeakTermEnum x)
substWeakTermPlus _ (m, WeakTermEnumIntro l) = do
  (m, WeakTermEnumIntro l)
substWeakTermPlus sub (m, WeakTermEnumElim (e, t) branchList) = do
  let t' = substWeakTermPlus sub t
  let e' = substWeakTermPlus sub e
  let (caseList, es) = unzip branchList
  let es' = map (substWeakTermPlus sub) es
  (m, WeakTermEnumElim (e', t') (zip caseList es'))
substWeakTermPlus sub (m, WeakTermArray dom k) = do
  let dom' = substWeakTermPlus sub dom
  (m, WeakTermArray dom' k)
substWeakTermPlus sub (m, WeakTermArrayIntro k es) = do
  let es' = map (substWeakTermPlus sub) es
  (m, WeakTermArrayIntro k es')
substWeakTermPlus sub (m, WeakTermArrayElim mk xts v e) = do
  let v' = substWeakTermPlus sub v
  let (xts', e') = substWeakTermPlus'' sub xts e
  (m, WeakTermArrayElim mk xts' v' e')
substWeakTermPlus _ (m, WeakTermStruct ts) = do
  (m, WeakTermStruct ts)
substWeakTermPlus sub (m, WeakTermStructIntro ets) = do
  let (es, ts) = unzip ets
  let es' = map (substWeakTermPlus sub) es
  (m, WeakTermStructIntro $ zip es' ts)
substWeakTermPlus sub (m, WeakTermStructElim xts v e) = do
  let v' = substWeakTermPlus sub v
  let xs = map (\(_, x, _) -> x) xts
  -- let sub' = filter (\(k, _) -> k `notElem` xs) sub
  let sub' = deleteKeys' sub (map (Left . asInt) xs)
  let e' = substWeakTermPlus sub' e
  (m, WeakTermStructElim xts v' e')
substWeakTermPlus sub (m, WeakTermCase indName e cxtes) = do
  let e' = substWeakTermPlus sub e
  let cxtes' =
        flip map cxtes $ \((c, xts), body) -> do
          let (xts', body') = substWeakTermPlus'' sub xts body
          ((c, xts'), body')
  (m, WeakTermCase indName e' cxtes')
substWeakTermPlus sub (m, WeakTermQuestion e t) = do
  let e' = substWeakTermPlus sub e
  let t' = substWeakTermPlus sub t
  (m, WeakTermQuestion e' t')
substWeakTermPlus sub (m, WeakTermErase xs e) = do
  let e' = substWeakTermPlus sub e
  (m, WeakTermErase xs e')

substWeakTermPlus' :: SubstWeakTerm -> [IdentifierPlus] -> [IdentifierPlus]
substWeakTermPlus' _ [] = []
substWeakTermPlus' sub ((m, x, t):xts)
  -- let sub' = filter (\(k, _) -> k /= x) sub
 = do
  let sub' = Map.delete (Left $ asInt x) sub
  let xts' = substWeakTermPlus' sub' xts
  let t' = substWeakTermPlus sub t
  (m, x, t') : xts'

substWeakTermPlus'' ::
     SubstWeakTerm
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> ([IdentifierPlus], WeakTermPlus)
substWeakTermPlus'' sub [] e = ([], substWeakTermPlus sub e)
substWeakTermPlus'' sub ((m, x, t):xts) e
  -- let sub' = filter (\(k, _) -> k /= x) sub
 = do
  let sub' = Map.delete (Left $ asInt x) sub
  let (xts', e') = substWeakTermPlus'' sub' xts e
  let t' = substWeakTermPlus sub t
  ((m, x, t') : xts', e')

metaOf :: WeakTermPlus -> Meta
metaOf e = fst e

asUpsilon :: WeakTermPlus -> Maybe Identifier
asUpsilon (_, WeakTermUpsilon x) = Just x
asUpsilon _ = Nothing

toText :: WeakTermPlus -> T.Text
toText (_, WeakTermTau) = "tau"
toText (_, WeakTermUpsilon x) = asText x
toText piType@(_, WeakTermPi Nothing xts cod) = do
  case extractSigmaArg piType of
    Just yts -> do
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
toText (_, WeakTermPi (Just _) _ cod) = toText cod
-- toText (m, WeakTermPi _ xts cod) = "+" <> toText (m, WeakTermPi Nothing xts cod)
toText (_, WeakTermPiIntro xts e) = do
  let argStr = inParen $ showItems $ map showArg xts
  showCons ["λ", argStr, toText e]
toText (_, WeakTermPiIntroPlus (name, _) _ _) = do
  "<#" <> name <> "-" <> "internal" <> "#>"
toText (_, WeakTermPiElim e es) = do
  showCons $ map toText $ e : es
toText (_, WeakTermIter (_, x, _) xts e) = do
  let argStr = inParen $ showItems $ map showArg xts
  showCons ["μ", asText x, argStr, toText e]
toText (_, WeakTermConst x) = x
toText (_, WeakTermZeta (I (_, i))) = "?M" <> T.pack (show i)
toText (_, WeakTermInt _ a) = T.pack $ show a
toText (_, WeakTermFloat _ a) = T.pack $ show a
toText (_, WeakTermEnum enumType) =
  case enumType of
    EnumTypeLabel l -> l
    EnumTypeIntS size -> "i" <> T.pack (show size)
    EnumTypeIntU size -> "u" <> T.pack (show size)
toText (_, WeakTermEnumIntro v) = showEnumValue v
toText (_, WeakTermEnumElim (e, _) mles) = do
  let (mls, es) = unzip mles
  let les = zip (map snd mls) es
  showCons ["case", toText e, showItems (map showClause les)]
toText (_, WeakTermArray dom k) =
  showCons ["array", toText dom, showArrayKind k]
toText (_, WeakTermArrayIntro _ es) = showArray $ map toText es
toText (_, WeakTermArrayElim _ xts e1 e2) = do
  let argStr = inParen $ showItems $ map showArg xts
  showCons ["array-elimination", argStr, toText e1, toText e2]
toText (_, WeakTermStruct ks) = showCons $ "struct" : map showArrayKind ks
toText (_, WeakTermStructIntro ets) = do
  showStruct $ map (toText . fst) ets
toText (_, WeakTermStructElim xts e1 e2) = do
  let argStr = inParen $ showItems $ map (\(_, x, _) -> asText x) xts
  showCons ["struct-elimination", argStr, toText e1, toText e2]
toText (_, WeakTermCase _ e cxtes) = do
  showCons
    ("case" :
     toText e :
     (flip map cxtes $ \((c, xts), body) -> do
        let xs = map (\(_, x, _) -> asText x) xts
        showCons [showCons ((snd c) : xs), toText body]))
toText (_, WeakTermQuestion e _) = toText e
toText (_, WeakTermErase _ e) = toText e

inParen :: T.Text -> T.Text
inParen s = "(" <> s <> ")"

inAngle :: T.Text -> T.Text
inAngle s = "<" <> s <> ">"

inBrace :: T.Text -> T.Text
inBrace s = "{" <> s <> "}"

inBracket :: T.Text -> T.Text
inBracket s = "[" <> s <> "]"

showArg :: (Meta, Identifier, WeakTermPlus) -> T.Text
showArg (_, x, t) = inParen $ asText x <> " " <> toText t

showTypeArgs :: [IdentifierPlus] -> WeakTermPlus -> T.Text
showTypeArgs [] _ = T.empty
showTypeArgs [(_, x, t)] cod
  | x `S.member` varWeakTermPlus cod = inParen $ asText x <> " " <> toText t
  | otherwise = inParen $ "_" <> " " <> toText t
showTypeArgs ((_, x, t):xts) cod
  | x `S.member` varWeakTermPlus' xts [cod] = do
    let s1 = inParen $ asText x <> " " <> toText t
    let s2 = showTypeArgs xts cod
    s1 <> " " <> s2
  | otherwise = do
    let s1 = inParen $ "_" <> " " <> toText t
    let s2 = showTypeArgs xts cod
    s1 <> " " <> s2

isDependent :: [IdentifierPlus] -> WeakTermPlus -> Bool
isDependent [] _ = False
isDependent ((_, x, _):xts) cod
  | x `S.member` varWeakTermPlus' xts [cod] = True
  | otherwise = isDependent xts cod

showClause :: (WeakCase, WeakTermPlus) -> T.Text
showClause (c, e) = inParen $ showWeakCase c <> " " <> toText e

showWeakCase :: WeakCase -> T.Text
showWeakCase (WeakCaseLabel l) = l
showWeakCase (WeakCaseIntS _ a) = T.pack $ show a
showWeakCase (WeakCaseIntU _ a) = T.pack $ show a
showWeakCase (WeakCaseInt _ a) = T.pack $ show a
showWeakCase WeakCaseDefault = "default"

weakenEnumValue :: EnumValue -> WeakCase
weakenEnumValue (EnumValueLabel l) = WeakCaseLabel l
weakenEnumValue (EnumValueIntS t a) = WeakCaseIntS t a
weakenEnumValue (EnumValueIntU t a) = WeakCaseIntU t a

showEnumValue :: EnumValue -> T.Text
showEnumValue (EnumValueLabel l) = l
showEnumValue (EnumValueIntS _ a) = T.pack $ show a
showEnumValue (EnumValueIntU _ a) = T.pack $ show a

showArrayKind :: ArrayKind -> T.Text
showArrayKind (ArrayKindIntS size) = T.pack $ "i" ++ show size
showArrayKind (ArrayKindIntU size) = T.pack $ "u" ++ show size
showArrayKind (ArrayKindFloat size) = T.pack $ "f" ++ show (sizeAsInt size)
showArrayKind ArrayKindVoidPtr = "void*"

showItems :: [T.Text] -> T.Text
showItems = T.intercalate " "

showCons :: [T.Text] -> T.Text
showCons = inParen . T.intercalate " "

showTuple :: [T.Text] -> T.Text
showTuple = inAngle . T.intercalate " "

showArray :: [T.Text] -> T.Text
showArray = inBracket . T.intercalate " "

showStruct :: [T.Text] -> T.Text
showStruct = inBrace . T.intercalate " "

extractSigmaArg :: WeakTermPlus -> Maybe [IdentifierPlus]
extractSigmaArg (_, WeakTermPi _ [(_, z, (_, WeakTermTau)), (_, _, (_, WeakTermPi _ xts (_, WeakTermUpsilon z')))] (_, WeakTermUpsilon z''))
  | z == z'
  , z == z'' = return xts
extractSigmaArg _ = Nothing

splitLast :: [a] -> Maybe ([a], a)
splitLast [] = Nothing
splitLast [x] = return ([], x)
splitLast (x:xs) = do
  (xs', z) <- splitLast xs
  return (x : xs', z)

type Key = Either Int T.Text

deleteKeys' :: Map.HashMap Key a -> [Key] -> Map.HashMap Key a
deleteKeys' sub [] = sub
deleteKeys' sub (i:is) = Map.delete i $ deleteKeys' sub is
