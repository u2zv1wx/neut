module Data.Term where

import Data.EnumCase
import Data.Ident
import qualified Data.IntMap as IntMap
import Data.LowType
import Data.Maybe (fromMaybe)
import Data.Meta
import Data.Size
import qualified Data.Text as T
import Data.WeakTerm

data Term
  = TermTau
  | TermUpsilon Ident
  | TermPi (Maybe T.Text) [IdentPlus] TermPlus
  | TermPiIntro (Maybe (Ident, T.Text, [IdentPlus])) [IdentPlus] TermPlus
  | TermPiElim TermPlus [TermPlus]
  | TermIter IdentPlus [IdentPlus] TermPlus
  | TermConst T.Text
  | TermBoxElim Ident -- S4 necessity
  | TermInt IntSize Integer
  | TermFloat FloatSize Double
  | TermEnum T.Text
  | TermEnumIntro T.Text
  | TermEnumElim (TermPlus, TermPlus) [(EnumCasePlus, TermPlus)]
  | TermArray TermPlus ArrayKind -- array n3 u8 ~= n3 -> u8
  | TermArrayIntro ArrayKind [TermPlus]
  | TermArrayElim
      ArrayKind
      [IdentPlus] -- [(x1, return t1), ..., (xn, return tn)] with xi : ti
      TermPlus
      TermPlus
  | TermStruct [ArrayKind] -- e.g. (struct u8 u8 f16 f32 u64)
  | TermStructIntro [(TermPlus, ArrayKind)]
  | TermStructElim [(Meta, Ident, ArrayKind)] TermPlus TermPlus
  | TermCase
      (Maybe Ident)
      TermPlus -- (the `e` in `case e of (...)`, the type of `e`)
      [Clause] -- ((cons x xs) e), ((nil) e), ((succ n) e).  (not ((cons A x xs) e).)
  deriving (Show)

type TextPlus =
  (Meta, T.Text, TermPlus)

type TermPlus =
  (Meta, Term)

type Clause =
  (((Meta, Ident), [IdentPlus]), TermPlus)

type SubstTerm =
  IntMap.IntMap TermPlus

type IdentPlus =
  (Meta, Ident, TermPlus)

data Stmt
  = StmtReturn Meta
  | StmtLet Meta IdentPlus TermPlus Stmt
  deriving (Show)

termPi :: [IdentPlus] -> TermPlus -> Term
termPi =
  TermPi Nothing

termPiIntro :: [IdentPlus] -> TermPlus -> Term
termPiIntro =
  TermPiIntro Nothing

asUpsilon :: TermPlus -> Maybe Ident
asUpsilon term =
  case term of
    (_, TermUpsilon x) ->
      Just x
    _ ->
      Nothing

varTermPlus :: TermPlus -> [Ident]
varTermPlus term =
  case term of
    (_, TermTau) ->
      []
    (_, TermUpsilon x) ->
      [x]
    (_, TermPi _ xts t) ->
      varTermPlus' xts [t]
    (_, TermPiIntro _ xts e) ->
      varTermPlus' xts [e]
    (_, TermPiElim e es) -> do
      let xs1 = varTermPlus e
      let xs2 = concatMap varTermPlus es
      xs1 ++ xs2
    (_, TermIter (_, x, t) xts e) ->
      varTermPlus t ++ filter (/= x) (varTermPlus' xts [e])
    (_, TermConst _) ->
      []
    (_, TermBoxElim _) ->
      []
    (_, TermInt _ _) ->
      []
    (_, TermFloat _ _) ->
      []
    (_, TermEnum _) ->
      []
    (_, TermEnumIntro _) ->
      []
    (_, TermEnumElim (e, t) les) -> do
      let xs0 = varTermPlus t
      let xs1 = varTermPlus e
      let es = map snd les
      let xs2 = concatMap varTermPlus es
      xs0 ++ xs1 ++ xs2
    (_, TermArray dom _) ->
      varTermPlus dom
    (_, TermArrayIntro _ es) ->
      concatMap varTermPlus es
    (_, TermArrayElim _ xts d e) ->
      varTermPlus d ++ varTermPlus' xts [e]
    (_, TermStruct {}) ->
      []
    (_, TermStructIntro ets) ->
      concatMap (varTermPlus . fst) ets
    (_, TermStructElim xts d e) -> do
      let xs = map (\(_, x, _) -> x) xts
      varTermPlus d ++ filter (`notElem` xs) (varTermPlus e)
    (_, TermCase _ e cxes) -> do
      let xs = varTermPlus e
      let ys = concatMap (\((_, xts), body) -> varTermPlus' xts [body]) cxes
      xs ++ ys

varTermPlus' :: [IdentPlus] -> [TermPlus] -> [Ident]
varTermPlus' binder es =
  case binder of
    [] ->
      concatMap varTermPlus es
    ((_, x, t) : xts) -> do
      let xs1 = varTermPlus t
      let xs2 = varTermPlus' xts es
      xs1 ++ filter (/= x) xs2

substTermPlus :: SubstTerm -> TermPlus -> TermPlus
substTermPlus sub term =
  case term of
    (m, TermTau) ->
      (m, TermTau)
    (m, TermUpsilon x) ->
      fromMaybe (m, TermUpsilon x) (IntMap.lookup (asInt x) sub)
    (m, TermPi mName xts t) -> do
      let (xts', t') = substTermPlus'' sub xts t
      (m, TermPi mName xts' t')
    (m, TermPiIntro info xts body) -> do
      let info' = fmap (fmap (substTermPlus' sub)) info
      let (xts', body') = substTermPlus'' sub xts body
      (m, TermPiIntro info' xts' body')
    (m, TermPiElim e es) -> do
      let e' = substTermPlus sub e
      let es' = map (substTermPlus sub) es
      (m, TermPiElim e' es')
    (m, TermIter (mx, x, t) xts e) -> do
      let t' = substTermPlus sub t
      let sub' = IntMap.delete (asInt x) sub
      let (xts', e') = substTermPlus'' sub' xts e
      (m, TermIter (mx, x, t') xts' e')
    e@(_, TermConst _) ->
      e
    e@(_, TermBoxElim _) ->
      e
    e@(_, TermInt _ _) ->
      e
    e@(_, TermFloat _ _) ->
      e
    (m, TermEnum x) ->
      (m, TermEnum x)
    (m, TermEnumIntro l) ->
      (m, TermEnumIntro l)
    (m, TermEnumElim (e, t) branchList) -> do
      let t' = substTermPlus sub t
      let e' = substTermPlus sub e
      let (caseList, es) = unzip branchList
      let es' = map (substTermPlus sub) es
      (m, TermEnumElim (e', t') (zip caseList es'))
    (m, TermArray dom k) -> do
      let dom' = substTermPlus sub dom
      (m, TermArray dom' k)
    (m, TermArrayIntro k es) -> do
      let es' = map (substTermPlus sub) es
      (m, TermArrayIntro k es')
    (m, TermArrayElim mk xts v e) -> do
      let v' = substTermPlus sub v
      let (xts', e') = substTermPlus'' sub xts e
      (m, TermArrayElim mk xts' v' e')
    (m, TermStruct ts) ->
      (m, TermStruct ts)
    (m, TermStructIntro ets) -> do
      let (es, ts) = unzip ets
      let es' = map (substTermPlus sub) es
      (m, TermStructIntro $ zip es' ts)
    (m, TermStructElim xts v e) -> do
      let v' = substTermPlus sub v
      let xs = map (\(_, x, _) -> asInt x) xts
      let sub' = foldr IntMap.delete sub xs
      let e' = substTermPlus sub' e
      (m, TermStructElim xts v' e')
    (m, TermCase indName e cxtes) -> do
      let e' = substTermPlus sub e
      let cxtes' =
            flip map cxtes $ \((c, xts), body) -> do
              let (xts', body') = substTermPlus'' sub xts body
              ((c, xts'), body')
      (m, TermCase indName e' cxtes')

substTermPlus' :: SubstTerm -> [IdentPlus] -> [IdentPlus]
substTermPlus' sub binder =
  case binder of
    [] ->
      []
    (m, x, t) : xts -> do
      let sub' = IntMap.delete (asInt x) sub
      let xts' = substTermPlus' sub' xts
      let t' = substTermPlus sub t
      (m, x, t') : xts'

substTermPlus'' :: SubstTerm -> [IdentPlus] -> TermPlus -> ([IdentPlus], TermPlus)
substTermPlus'' sub binder e =
  case binder of
    [] ->
      ([], substTermPlus sub e)
    (mx, x, t) : xts -> do
      let sub' = IntMap.delete (asInt x) sub
      let (xts', e') = substTermPlus'' sub' xts e
      ((mx, x, substTermPlus sub t) : xts', e')

weaken :: TermPlus -> WeakTermPlus
weaken term =
  case term of
    (m, TermTau) ->
      (m, WeakTermTau)
    (m, TermUpsilon x) ->
      (m, WeakTermUpsilon x)
    (m, TermPi mName xts t) ->
      (m, WeakTermPi mName (weakenArgs xts) (weaken t))
    (m, TermPiIntro info xts body) -> do
      let info' = fmap (fmap weakenArgs) info
      let xts' = weakenArgs xts
      (m, WeakTermPiIntro info' xts' (weaken body))
    (m, TermPiElim e es) -> do
      let e' = weaken e
      let es' = map weaken es
      (m, WeakTermPiElim e' es')
    (m, TermIter (mx, x, t) xts e) -> do
      let t' = weaken t
      let xts' = weakenArgs xts
      let e' = weaken e
      (m, WeakTermIter (mx, x, t') xts' e')
    (m, TermConst x) ->
      (m, WeakTermConst x)
    (m, TermBoxElim x) ->
      (m, WeakTermBoxElim x)
    (m, TermInt size x) ->
      (m, WeakTermInt (m, WeakTermConst (showIntSize size)) x)
    (m, TermFloat size x) ->
      (m, WeakTermFloat (m, WeakTermConst (showFloatSize size)) x)
    (m, TermEnum x) ->
      (m, WeakTermEnum x)
    (m, TermEnumIntro l) ->
      (m, WeakTermEnumIntro l)
    (m, TermEnumElim (e, t) branchList) -> do
      let t' = weaken t
      let e' = weaken e
      let (caseList, es) = unzip branchList
      let es' = map weaken es
      (m, WeakTermEnumElim (e', t') (zip caseList es'))
    (m, TermArray dom k) -> do
      let dom' = weaken dom
      (m, WeakTermArray dom' k)
    (m, TermArrayIntro k es) -> do
      let es' = map weaken es
      (m, WeakTermArrayIntro k es')
    (m, TermArrayElim mk xts v e) -> do
      let v' = weaken v
      let xts' = weakenArgs xts
      let e' = weaken e
      (m, WeakTermArrayElim mk xts' v' e')
    (m, TermStruct ts) ->
      (m, WeakTermStruct ts)
    (m, TermStructIntro ets) -> do
      let (es, ts) = unzip ets
      let es' = map weaken es
      (m, WeakTermStructIntro $ zip es' ts)
    (m, TermStructElim xts v e) -> do
      let v' = weaken v
      let e' = weaken e
      (m, WeakTermStructElim xts v' e')
    (m, TermCase indName e cxtes) -> do
      let e' = weaken e
      let cxtes' =
            flip map cxtes $ \((c, xts), body) -> do
              let xts' = weakenArgs xts
              let body' = weaken body
              ((c, xts'), body')
      (m, WeakTermCase indName e' cxtes')

weakenArgs :: [(Meta, Ident, TermPlus)] -> [(Meta, Ident, WeakTermPlus)]
weakenArgs xts = do
  let (ms, xs, ts) = unzip3 xts
  zip3 ms xs (map weaken ts)
