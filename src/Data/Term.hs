module Data.Term where

import Data.Basic
import Data.Binary
import qualified Data.IntMap as IntMap
import Data.Maybe (fromMaybe)
import qualified Data.Text as T
import Data.WeakTerm
import GHC.Generics (Generic)

data Term
  = TermTau
  | TermUpsilon Ident
  | TermPi (Maybe T.Text) [IdentPlus] TermPlus
  | TermPiIntro (Maybe (Ident, T.Text, [IdentPlus])) [IdentPlus] TermPlus
  | TermPiElim TermPlus [TermPlus]
  | TermIter IdentPlus [IdentPlus] TermPlus
  | TermConst T.Text
  | TermBoxElim Ident -- S4 necessity
  | TermFloat FloatSize Double
  | TermEnum EnumType
  | TermEnumIntro EnumValue
  | TermEnumElim (TermPlus, TermPlus) [(CasePlus, TermPlus)]
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
  deriving (Show, Generic)

instance Binary Term

type TextPlus = (Meta, T.Text, TermPlus)

type TermPlus = (Meta, Term)

type Clause = (((Meta, Ident), [IdentPlus]), TermPlus)

type SubstTerm = IntMap.IntMap TermPlus

type IdentPlus = (Meta, Ident, TermPlus)

data Stmt
  = StmtReturn Meta
  | StmtLet Meta IdentPlus TermPlus Stmt
  deriving (Show)

termPi :: [IdentPlus] -> TermPlus -> Term
termPi = TermPi Nothing

termPiIntro :: [IdentPlus] -> TermPlus -> Term
termPiIntro = TermPiIntro Nothing

asUpsilon :: TermPlus -> Maybe Ident
asUpsilon (_, TermUpsilon x) = Just x
asUpsilon _ = Nothing

varTermPlus :: TermPlus -> [Ident]
varTermPlus (_, TermTau) = []
varTermPlus (_, TermUpsilon x) = [x]
varTermPlus (_, TermPi _ xts t) = varTermPlus' xts [t]
varTermPlus (_, TermPiIntro _ xts e) = varTermPlus' xts [e]
varTermPlus (_, TermPiElim e es) = do
  let xs1 = varTermPlus e
  let xs2 = concatMap varTermPlus es
  xs1 ++ xs2
varTermPlus (_, TermIter (_, x, t) xts e) =
  varTermPlus t ++ filter (/= x) (varTermPlus' xts [e])
varTermPlus (_, TermConst _) = []
varTermPlus (_, TermBoxElim _) = []
varTermPlus (_, TermFloat _ _) = []
varTermPlus (_, TermEnum _) = []
varTermPlus (_, TermEnumIntro _) = []
varTermPlus (_, TermEnumElim (e, t) les) = do
  let xs0 = varTermPlus t
  let xs1 = varTermPlus e
  let es = map snd les
  let xs2 = concatMap varTermPlus es
  xs0 ++ xs1 ++ xs2
varTermPlus (_, TermArray dom _) = varTermPlus dom
varTermPlus (_, TermArrayIntro _ es) =
  concatMap varTermPlus es
varTermPlus (_, TermArrayElim _ xts d e) = varTermPlus d ++ varTermPlus' xts [e]
varTermPlus (_, TermStruct {}) = []
varTermPlus (_, TermStructIntro ets) = concatMap (varTermPlus . fst) ets
varTermPlus (_, TermStructElim xts d e) = do
  let xs = map (\(_, x, _) -> x) xts
  varTermPlus d ++ filter (`notElem` xs) (varTermPlus e)
varTermPlus (_, TermCase _ e cxes) = do
  let xs = varTermPlus e
  let ys = concatMap (\((_, xts), body) -> varTermPlus' xts [body]) cxes
  xs ++ ys

varTermPlus' :: [IdentPlus] -> [TermPlus] -> [Ident]
varTermPlus' [] es = concatMap varTermPlus es
varTermPlus' ((_, x, t) : xts) es = do
  let xs1 = varTermPlus t
  let xs2 = varTermPlus' xts es
  xs1 ++ filter (/= x) xs2

substTermPlus :: SubstTerm -> TermPlus -> TermPlus
substTermPlus _ (m, TermTau) = (m, TermTau)
substTermPlus sub (m, TermUpsilon x) =
  fromMaybe (m, TermUpsilon x) (IntMap.lookup (asInt x) sub)
substTermPlus sub (m, TermPi mName xts t) = do
  let (xts', t') = substTermPlus'' sub xts t
  (m, TermPi mName xts' t')
substTermPlus sub (m, TermPiIntro info xts body) = do
  let info' = fmap2 (substTermPlus' sub) info
  let (xts', body') = substTermPlus'' sub xts body
  (m, TermPiIntro info' xts' body')
substTermPlus sub (m, TermPiElim e es) = do
  let e' = substTermPlus sub e
  let es' = map (substTermPlus sub) es
  (m, TermPiElim e' es')
substTermPlus sub (m, TermIter (mx, x, t) xts e) = do
  let t' = substTermPlus sub t
  let sub' = IntMap.delete (asInt x) sub
  let (xts', e') = substTermPlus'' sub' xts e
  (m, TermIter (mx, x, t') xts' e')
substTermPlus _ e@(_, TermConst _) = e
substTermPlus _ e@(_, TermBoxElim _) = e
substTermPlus _ e@(_, TermFloat _ _) = e
substTermPlus _ (m, TermEnum x) = (m, TermEnum x)
substTermPlus _ (m, TermEnumIntro l) = (m, TermEnumIntro l)
substTermPlus sub (m, TermEnumElim (e, t) branchList) = do
  let t' = substTermPlus sub t
  let e' = substTermPlus sub e
  let (caseList, es) = unzip branchList
  let es' = map (substTermPlus sub) es
  (m, TermEnumElim (e', t') (zip caseList es'))
substTermPlus sub (m, TermArray dom k) = do
  let dom' = substTermPlus sub dom
  (m, TermArray dom' k)
substTermPlus sub (m, TermArrayIntro k es) = do
  let es' = map (substTermPlus sub) es
  (m, TermArrayIntro k es')
substTermPlus sub (m, TermArrayElim mk xts v e) = do
  let v' = substTermPlus sub v
  let (xts', e') = substTermPlus'' sub xts e
  (m, TermArrayElim mk xts' v' e')
substTermPlus _ (m, TermStruct ts) =
  (m, TermStruct ts)
substTermPlus sub (m, TermStructIntro ets) = do
  let (es, ts) = unzip ets
  let es' = map (substTermPlus sub) es
  (m, TermStructIntro $ zip es' ts)
substTermPlus sub (m, TermStructElim xts v e) = do
  let v' = substTermPlus sub v
  let xs = map (\(_, x, _) -> asInt x) xts
  let sub' = deleteKeys sub xs
  let e' = substTermPlus sub' e
  (m, TermStructElim xts v' e')
substTermPlus sub (m, TermCase indName e cxtes) = do
  let e' = substTermPlus sub e
  let cxtes' =
        flip map cxtes $ \((c, xts), body) -> do
          let (xts', body') = substTermPlus'' sub xts body
          ((c, xts'), body')
  (m, TermCase indName e' cxtes')

substTermPlus' :: SubstTerm -> [IdentPlus] -> [IdentPlus]
substTermPlus' _ [] = []
substTermPlus' sub ((m, x, t) : xts) = do
  let sub' = IntMap.delete (asInt x) sub
  let xts' = substTermPlus' sub' xts
  let t' = substTermPlus sub t
  (m, x, t') : xts'

substTermPlus'' ::
  SubstTerm -> [IdentPlus] -> TermPlus -> ([IdentPlus], TermPlus)
substTermPlus'' sub [] e = ([], substTermPlus sub e)
substTermPlus'' sub ((mx, x, t) : xts) e = do
  let sub' = IntMap.delete (asInt x) sub
  let (xts', e') = substTermPlus'' sub' xts e
  ((mx, x, substTermPlus sub t) : xts', e')

weaken :: TermPlus -> WeakTermPlus
weaken (m, TermTau) = (m, WeakTermTau)
weaken (m, TermUpsilon x) = (m, WeakTermUpsilon x)
weaken (m, TermPi mName xts t) =
  (m, WeakTermPi mName (weakenArgs xts) (weaken t))
weaken (m, TermPiIntro info xts body) = do
  let info' = fmap2 weakenArgs info
  let xts' = weakenArgs xts
  (m, WeakTermPiIntro info' xts' (weaken body))
weaken (m, TermPiElim e es) = do
  let e' = weaken e
  let es' = map weaken es
  (m, WeakTermPiElim e' es')
weaken (m, TermIter (mx, x, t) xts e) = do
  let t' = weaken t
  let xts' = weakenArgs xts
  let e' = weaken e
  (m, WeakTermIter (mx, x, t') xts' e')
weaken (m, TermConst x) = (m, WeakTermConst x)
weaken (m, TermBoxElim x) = (m, WeakTermBoxElim x)
weaken (m, TermFloat size x) =
  (m, WeakTermFloat (m, WeakTermConst ("f" <> showFloatSize size)) x)
weaken (m, TermEnum x) = (m, WeakTermEnum x)
weaken (m, TermEnumIntro l) = (m, WeakTermEnumIntro l)
weaken (m, TermEnumElim (e, t) branchList) = do
  let t' = weaken t
  let e' = weaken e
  let (caseList, es) = unzip branchList
  let caseList' = map weakenCase caseList
  let es' = map weaken es
  (m, WeakTermEnumElim (e', t') (zip caseList' es'))
weaken (m, TermArray dom k) = do
  let dom' = weaken dom
  (m, WeakTermArray dom' k)
weaken (m, TermArrayIntro k es) = do
  let es' = map weaken es
  (m, WeakTermArrayIntro k es')
weaken (m, TermArrayElim mk xts v e) = do
  let v' = weaken v
  let xts' = weakenArgs xts
  let e' = weaken e
  (m, WeakTermArrayElim mk xts' v' e')
weaken (m, TermStruct ts) =
  (m, WeakTermStruct ts)
weaken (m, TermStructIntro ets) = do
  let (es, ts) = unzip ets
  let es' = map weaken es
  (m, WeakTermStructIntro $ zip es' ts)
weaken (m, TermStructElim xts v e) = do
  let v' = weaken v
  let e' = weaken e
  (m, WeakTermStructElim xts v' e')
weaken (m, TermCase indName e cxtes) = do
  let e' = weaken e
  let cxtes' =
        flip map cxtes $ \((c, xts), body) -> do
          let xts' = weakenArgs xts
          let body' = weaken body
          ((c, xts'), body')
  (m, WeakTermCase indName e' cxtes')

weakenCase :: CasePlus -> WeakCasePlus
weakenCase (m, CaseValue v) = (m, weakenEnumValue v)
weakenCase (m, CaseDefault) = (m, WeakCaseDefault)

weakenArgs ::
  [(Meta, Ident, TermPlus)] -> [(Meta, Ident, WeakTermPlus)]
weakenArgs xts = do
  let (ms, xs, ts) = unzip3 xts
  zip3 ms xs (map weaken ts)
