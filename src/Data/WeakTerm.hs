{-# LANGUAGE OverloadedStrings #-}

module Data.WeakTerm where

import Numeric.Half

import qualified Data.Text as T

import Data.Basic

-- VectorをSigma[A, ..., A]の略記として入れてもいいかも。
-- clarifyの時点でSigmaに落とす。
data WeakTerm
  = WeakTermTau UnivLevel
  | WeakTermUpsilon Identifier
  | WeakTermPi [UnivLevelPlus] [IdentifierPlus] WeakTermPlus
  | WeakTermPiPlus T.Text [UnivLevelPlus] [IdentifierPlus] WeakTermPlus
  | WeakTermPiIntro [IdentifierPlus] WeakTermPlus
  | WeakTermPiIntroPlus
      T.Text -- name of constructor
      T.Text -- name of inductive type
      WeakFVInfo
      [IdentifierPlus]
      WeakTermPlus
  | WeakTermPiElim WeakTermPlus [WeakTermPlus]
  -- We define Sigma here since n-ary Sigma cannot be defined in the target language.
  -- Although we can `define` it using `notation`, it makes the output of type error
  -- harder to read. Also, by explicitly introducing Sigma as a syntactic construct,
  -- the type inference of Sigma becomes a little more efficient. So we chose to define
  -- it as a syntactic construct.
  -- Of course, we can define 2-ary Sigma and use it to express n-ary Sigma. However,
  -- it sacrifices the performance of output code. I don't choose that way.
  -- Note that this "Sigma" is decomposed into Pi in the standard way that you see in CoC after type inference.
  -- (sigma (x1 A1) ... (xn An))
  | WeakTermSigma [IdentifierPlus]
  -- (sigma-intro type-of-this-sigma-intro e1 ... en)
  -- type-annotation is required when this construct is translated into Pi in elaboration.
  | WeakTermSigmaIntro WeakTermPlus [WeakTermPlus]
  -- (sigma-elimination type-of-e2 ((x1 A1) ... (xn An)) e1 e2)
  -- again, type-annotation is required when this construct is translated into Pi in elaboration.
  | WeakTermSigmaElim WeakTermPlus [IdentifierPlus] WeakTermPlus WeakTermPlus
  -- CBN recursion ~ CBV iteration
  | WeakTermIter IdentifierPlus [IdentifierPlus] WeakTermPlus
  | WeakTermZeta Identifier
  | WeakTermConst Identifier
  | WeakTermInt WeakTermPlus Integer
  | WeakTermFloat16 Half
  | WeakTermFloat32 Float
  | WeakTermFloat64 Double
  | WeakTermFloat WeakTermPlus Double
  | WeakTermEnum EnumType
  | WeakTermEnumIntro EnumValue
  | WeakTermEnumElim (WeakTermPlus, WeakTermPlus) [(WeakCase, WeakTermPlus)]
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
  -- µF -> FµF -> A (the isomorphism in Lambek's lemma + ordinary function from the coproduct FµF (i.e. pattern matching))
  -- this syntactic construct is only for performance improvement, and doesn't enhance the expressiveness of the type system.
  -- it might also make sense to add only the isomorphism part `µF -> FµF`, and let the user write the other part.
  -- one might even think that this way is preferable from the viewpoint of theoretical virtue.
  -- but I don't feel like doing so (at least for now) because this `case` construct is already just an optimization technique.
  | WeakTermCase
      (WeakTermPlus, WeakTermPlus) -- (the `e` in `case e of (...)`, the type of `e`)
      [((Identifier, [IdentifierPlus]), WeakTermPlus)] -- ((cons x xs) e), ((nil) e), ((succ n) e).  (not ((cons A x xs) e).)
  -- A -> FνF -> νF (i.e. copattern matching (although I think it's more correct to say "record" or something like that,
  -- considering that the constructed term using `FνF -> νF` is just a record after all))
  -- this syntactic construct is only for performance improvement, too.
  -- (cocase c (c e) ... (c e))
  -- | WeakTermCocase
  --     [Identifier] -- the list of mutually defined coinductive types
  --     (Identifier, [WeakTermPlus]) -- a @ (e, ..., e)  (e.g. stream @ A)
  --     [(Identifier, WeakTermPlus)] -- (some-label any-term)
  deriving (Show, Eq)

type WeakTermPlus = (Meta, WeakTerm)

data WeakCase
  = WeakCaseIntS IntSize Integer
  | WeakCaseIntU IntSize Integer
  | WeakCaseInt WeakTermPlus Integer
  | WeakCaseLabel T.Text
  | WeakCaseDefault
  deriving (Show, Eq)

type SubstWeakTerm = [(Identifier, WeakTermPlus)]

type WeakFVInfo = [(Identifier, (WeakTermPlus, WeakTermPlus))]

asSubst :: WeakFVInfo -> SubstWeakTerm
asSubst info = do
  let (zs, ets) = unzip info
  zip zs (map fst ets)

type Hole = Identifier

type IdentifierPlus = (Meta, Identifier, WeakTermPlus)

type Def = (Meta, IdentifierPlus, [IdentifierPlus], WeakTermPlus)

type IdentDef = (Identifier, Def)

type Rule -- inference rule
   = ( Meta -- location of the name
     , Identifier -- the name of the rule
     , Meta -- location of the rule
     , [IdentifierPlus] -- the antecedents of the inference rule (e.g. [(x, A), (xs, list A)])
     , WeakTermPlus -- the consequent of the inference rule
      )

type Connective
   = ( Meta -- location of the connective
     , Identifier -- the name of the connective (e.g. nat, list)
     , [IdentifierPlus] -- parameter of the connective (e.g. the `A` in `list A`)
     , [Rule] -- list of introduction rule when inductive / list of elimination rule when coinductive
      )

data QuasiStmt
  -- translated intro lam + app as in the usual way
  --   (let (x t) e)
  = QuasiStmtLet Meta IdentifierPlus WeakTermPlus
  -- special case of `let` in which the `e` in `let x := e` is known to be well-typed
  | QuasiStmtLetWT Meta IdentifierPlus WeakTermPlus
  -- mutually recursive definition (n >= 0)
  --   (definition
  --     ((f1 A1) (ARGS-1) e1)
  --     ...
  --     ((fn An) (ARGS-n) en))
  | QuasiStmtDef [(Identifier, Def)]
  -- declaration of a constant
  --   (constant x t)
  | QuasiStmtConstDecl Meta IdentifierPlus
  | QuasiStmtLetInductive Int Meta IdentifierPlus WeakTermPlus
  | QuasiStmtLetCoinductive Int Meta IdentifierPlus WeakTermPlus
  -- let (b : B) :=
  --   lam (xts ++ yts).
  --     lam (ats ++ bts).
  --       b-inner @ [y, ..., y]
  | QuasiStmtLetInductiveIntro
      Meta -- location of b
      (T.Text, T.Text) -- ("zero", "nat") (i.e. enum info)
      IdentifierPlus -- b : B
      [IdentifierPlus] -- xts
      [IdentifierPlus] -- yts
      [IdentifierPlus] -- ats
      [IdentifierPlus] -- bts
      WeakTermPlus -- b-inner
      -- [IdentifierPlus] -- [(y, t), ..., (y, t)]  (must be internalized later)
      SubstWeakTerm -- the `a` in `ats` ~> the `a` defined beforehand
      [Identifier] -- as (to be used to update the environment with constructor info)
  -- let (b : B) :=
  --   lam (xts ++ [(z, t)]).
  --     let (ats ++ bts ++ [(c, t)]) := z in
  --     b-inner @ [c]
  | QuasiStmtLetCoinductiveElim
      Meta
      IdentifierPlus
      [IdentifierPlus] -- xts ++ [(z, t)]
      WeakTermPlus -- the type of b-inner @ [c]                  --
      [IdentifierPlus] -- ats                                    --
      [IdentifierPlus] -- bts                                    -- sigma-elim
      IdentifierPlus -- (c, t)                                   --
      WeakTermPlus -- z                                          --
      WeakTermPlus -- b-inner @ [c] (must be externalized later) --
      SubstWeakTerm -- the `a` defined beforehand ~> the `a` in `ats`
      [Identifier] -- as (to be used to update the environment with constructor info)
  deriving (Show)

data WeakStmt
  = WeakStmtReturn WeakTermPlus
  | WeakStmtLet Meta IdentifierPlus WeakTermPlus WeakStmt
  -- special case of `let` in which the `e` in `let x := e in cont` is known to be well-typed
  | WeakStmtLetWT Meta IdentifierPlus WeakTermPlus WeakStmt
  | WeakStmtLetInductiveIntro
      Meta -- m
      (T.Text, T.Text) -- biai
      IdentifierPlus -- bt
      [IdentifierPlus] -- yts
      [IdentifierPlus] -- yts
      [IdentifierPlus] -- atsbts
      WeakTermPlus -- bInner @ yts'
      WeakStmt -- cont
  | WeakStmtConstDecl Meta IdentifierPlus WeakStmt
  deriving (Show)

toVar :: Identifier -> WeakTermPlus
toVar x = (emptyMeta, WeakTermUpsilon x)

varWeakTermPlus :: WeakTermPlus -> [Identifier]
varWeakTermPlus (_, WeakTermTau _) = []
varWeakTermPlus (_, WeakTermUpsilon x) = x : []
varWeakTermPlus (_, WeakTermPi _ xts t) = varWeakTermPlus' xts [t]
varWeakTermPlus (_, WeakTermPiPlus _ _ xts t) = varWeakTermPlus' xts [t]
varWeakTermPlus (_, WeakTermPiIntro xts e) = varWeakTermPlus' xts [e]
varWeakTermPlus (_, WeakTermPiIntroPlus _ _ sub xts e) = do
  let ys = varWeakTermPlus' xts [e]
  -- let (zs, es) = unzip sub
  let (zs, ees) = unzip sub
  let (es1, es2) = unzip ees
  filter (`notElem` zs) ys ++ concatMap varWeakTermPlus (es1 ++ es2)
varWeakTermPlus (_, WeakTermPiElim e es) = do
  let xs = varWeakTermPlus e
  let ys = concatMap varWeakTermPlus es
  xs ++ ys
varWeakTermPlus (_, WeakTermSigma xts) = varWeakTermPlus' xts []
varWeakTermPlus (_, WeakTermSigmaIntro t es) = do
  varWeakTermPlus t ++ concatMap varWeakTermPlus es
varWeakTermPlus (_, WeakTermSigmaElim t xts e1 e2) = do
  let xs = varWeakTermPlus t
  let ys = varWeakTermPlus e1
  let zs = varWeakTermPlus' xts [e2]
  xs ++ ys ++ zs
varWeakTermPlus (_, WeakTermIter (_, x, t) xts e) =
  varWeakTermPlus t ++ filter (/= x) (varWeakTermPlus' xts [e])
varWeakTermPlus (_, WeakTermConst _) = []
varWeakTermPlus (_, WeakTermZeta _) = []
varWeakTermPlus (_, WeakTermInt t _) = varWeakTermPlus t
varWeakTermPlus (_, WeakTermFloat16 _) = []
varWeakTermPlus (_, WeakTermFloat32 _) = []
varWeakTermPlus (_, WeakTermFloat64 _) = []
varWeakTermPlus (_, WeakTermFloat t _) = varWeakTermPlus t
varWeakTermPlus (_, WeakTermEnum _) = []
varWeakTermPlus (_, WeakTermEnumIntro _) = []
varWeakTermPlus (_, WeakTermEnumElim (e, t) les) = do
  let xs = varWeakTermPlus t
  let ys = varWeakTermPlus e
  let zs = concatMap (varWeakTermPlus . snd) les
  xs ++ ys ++ zs
varWeakTermPlus (_, WeakTermArray dom _) = varWeakTermPlus dom
varWeakTermPlus (_, WeakTermArrayIntro _ es) = concatMap varWeakTermPlus es
varWeakTermPlus (_, WeakTermArrayElim _ xts d e) =
  varWeakTermPlus d ++ varWeakTermPlus' xts [e]
varWeakTermPlus (_, WeakTermStruct {}) = []
varWeakTermPlus (_, WeakTermStructIntro ets) =
  concatMap (varWeakTermPlus . fst) ets
varWeakTermPlus (_, WeakTermStructElim xts d e) = do
  let xs = map (\(_, x, _) -> x) xts
  varWeakTermPlus d ++ filter (`notElem` xs) (varWeakTermPlus e)
varWeakTermPlus (_, WeakTermCase (e, t) cxes) = do
  let xs = varWeakTermPlus e
  let ys = varWeakTermPlus t
  let zs = concatMap (\((_, xts), body) -> varWeakTermPlus' xts [body]) cxes
  xs ++ ys ++ zs

-- varWeakTermPlus (_, WeakTermCocase as (_, es) ces) =
--   as ++ (concatMap varWeakTermPlus $ es ++ map snd ces)
varWeakTermPlus' :: [IdentifierPlus] -> [WeakTermPlus] -> [Identifier]
varWeakTermPlus' [] es = concatMap varWeakTermPlus es
varWeakTermPlus' ((_, x, t):xts) es = do
  let hs1 = varWeakTermPlus t
  let hs2 = varWeakTermPlus' xts es
  hs1 ++ filter (/= x) hs2

holeWeakTermPlus :: WeakTermPlus -> [Hole]
holeWeakTermPlus (_, WeakTermTau _) = []
holeWeakTermPlus (_, WeakTermUpsilon _) = []
holeWeakTermPlus (_, WeakTermPi _ xts t) = holeWeakTermPlus' xts [t]
holeWeakTermPlus (_, WeakTermPiPlus _ _ xts t) = holeWeakTermPlus' xts [t]
holeWeakTermPlus (_, WeakTermPiIntro xts e) = holeWeakTermPlus' xts [e]
holeWeakTermPlus (_, WeakTermPiIntroPlus _ _ sub xts e) = do
  let ys = holeWeakTermPlus' xts [e]
  let (_, ees) = unzip sub
  let (es1, es2) = unzip ees
  ys ++ concatMap holeWeakTermPlus (es1 ++ es2)
holeWeakTermPlus (_, WeakTermPiElim e es) =
  holeWeakTermPlus e ++ concatMap holeWeakTermPlus es
holeWeakTermPlus (_, WeakTermSigma xts) = holeWeakTermPlus' xts []
holeWeakTermPlus (_, WeakTermSigmaIntro t es) =
  holeWeakTermPlus t ++ concatMap holeWeakTermPlus es
holeWeakTermPlus (_, WeakTermSigmaElim t xts e1 e2) = do
  let xs = holeWeakTermPlus t
  let ys = holeWeakTermPlus e1
  let zs = holeWeakTermPlus' xts [e2]
  xs ++ ys ++ zs
holeWeakTermPlus (_, WeakTermIter (_, _, t) xts e) =
  holeWeakTermPlus t ++ holeWeakTermPlus' xts [e]
holeWeakTermPlus (_, WeakTermZeta h) = h : []
holeWeakTermPlus (_, WeakTermConst _) = []
holeWeakTermPlus (_, WeakTermInt t _) = holeWeakTermPlus t
holeWeakTermPlus (_, WeakTermFloat16 _) = []
holeWeakTermPlus (_, WeakTermFloat32 _) = []
holeWeakTermPlus (_, WeakTermFloat64 _) = []
holeWeakTermPlus (_, WeakTermFloat t _) = holeWeakTermPlus t
holeWeakTermPlus (_, WeakTermEnum _) = []
holeWeakTermPlus (_, WeakTermEnumIntro _) = []
holeWeakTermPlus (_, WeakTermEnumElim (e, t) les) = do
  let xs = holeWeakTermPlus e
  let ys = holeWeakTermPlus t
  let zs = concatMap (\(_, body) -> holeWeakTermPlus body) les
  xs ++ ys ++ zs
holeWeakTermPlus (_, WeakTermArray dom _) = holeWeakTermPlus dom
holeWeakTermPlus (_, WeakTermArrayIntro _ es) = concatMap holeWeakTermPlus es
holeWeakTermPlus (_, WeakTermArrayElim _ xts d e) =
  holeWeakTermPlus d ++ holeWeakTermPlus' xts [e]
holeWeakTermPlus (_, WeakTermStruct {}) = []
holeWeakTermPlus (_, WeakTermStructIntro ets) =
  concatMap (holeWeakTermPlus . fst) ets
holeWeakTermPlus (_, WeakTermStructElim _ d e) =
  holeWeakTermPlus d ++ holeWeakTermPlus e
holeWeakTermPlus (_, WeakTermCase (e, t) cxes) = do
  let xs = holeWeakTermPlus e
  let ys = holeWeakTermPlus t
  let zs = concatMap (\((_, xts), body) -> holeWeakTermPlus' xts [body]) cxes
  xs ++ ys ++ zs

-- holeWeakTermPlus (_, WeakTermCocase _ (_, es) ces) =
--   concatMap holeWeakTermPlus $ es ++ map snd ces
holeWeakTermPlus' :: [IdentifierPlus] -> [WeakTermPlus] -> [Hole]
holeWeakTermPlus' [] es = concatMap holeWeakTermPlus es
holeWeakTermPlus' ((_, _, t):xts) es =
  holeWeakTermPlus t ++ holeWeakTermPlus' xts es

substWeakTermPlus :: SubstWeakTerm -> WeakTermPlus -> WeakTermPlus
substWeakTermPlus _ tau@(_, WeakTermTau _) = tau
substWeakTermPlus sub e1@(_, WeakTermUpsilon x) = do
  case lookup x sub of
    Nothing -> e1
    Just e2@(_, e) -> (supMeta (metaOf e1) (metaOf e2), e)
substWeakTermPlus sub (m, WeakTermPi mls xts t) = do
  let (xts', t') = substWeakTermPlus'' sub xts t
  (m, WeakTermPi mls xts' t')
substWeakTermPlus sub (m, WeakTermPiPlus name mls xts t) = do
  let (xts', t') = substWeakTermPlus'' sub xts t
  (m, WeakTermPiPlus name mls xts' t')
substWeakTermPlus sub (m, WeakTermPiIntro xts body) = do
  let (xts', body') = substWeakTermPlus'' sub xts body
  (m, WeakTermPiIntro xts' body')
substWeakTermPlus sub (m, WeakTermPiIntroPlus name indName s xts body) = do
  let sub' = filter (\(k, _) -> k `notElem` map fst s) sub -- lamに含まれる自由変数のうちsで「保護」されているものは無視
  let (xts', body') = substWeakTermPlus'' sub' xts body
  let (zs, ees) = unzip s
  let (es1, es2) = unzip ees
  let es1' = map (substWeakTermPlus sub) es1 -- s自体の更新は行なう
  let es2' = map (substWeakTermPlus sub) es2
  (m, WeakTermPiIntroPlus name indName (zip zs (zip es1' es2')) xts' body')
substWeakTermPlus sub (m, WeakTermPiElim e es) = do
  let e' = substWeakTermPlus sub e
  let es' = map (substWeakTermPlus sub) es
  (m, WeakTermPiElim e' es')
substWeakTermPlus sub (m, WeakTermSigma xts) = do
  let xts' = substWeakTermPlus' sub xts
  (m, WeakTermSigma xts')
substWeakTermPlus sub (m, WeakTermSigmaIntro t es) = do
  let t' = substWeakTermPlus sub t
  let es' = map (substWeakTermPlus sub) es
  (m, WeakTermSigmaIntro t' es')
substWeakTermPlus sub (m, WeakTermSigmaElim t xts e1 e2) = do
  let t' = substWeakTermPlus sub t
  let e1' = substWeakTermPlus sub e1
  let (xts', e2') = substWeakTermPlus'' sub xts e2
  (m, WeakTermSigmaElim t' xts' e1' e2')
substWeakTermPlus sub (m, WeakTermIter (mx, x, t) xts e) = do
  let t' = substWeakTermPlus sub t
  let sub' = filter (\(k, _) -> k /= x) sub
  let (xts', e') = substWeakTermPlus'' sub' xts e
  (m, WeakTermIter (mx, x, t') xts' e')
substWeakTermPlus _ (m, WeakTermConst x) = (m, WeakTermConst x)
substWeakTermPlus sub e1@(_, WeakTermZeta x) = do
  case lookup x sub of
    Nothing -> e1
    Just e2@(_, e) -> (supMeta (metaOf e1) (metaOf e2), e)
substWeakTermPlus sub (m, WeakTermInt t x) = do
  let t' = substWeakTermPlus sub t
  (m, WeakTermInt t' x)
substWeakTermPlus _ (m, WeakTermFloat16 x) = do
  (m, WeakTermFloat16 x)
substWeakTermPlus _ (m, WeakTermFloat32 x) = do
  (m, WeakTermFloat32 x)
substWeakTermPlus _ (m, WeakTermFloat64 x) = do
  (m, WeakTermFloat64 x)
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
  let sub' = filter (\(k, _) -> k `notElem` xs) sub
  let e' = substWeakTermPlus sub' e
  (m, WeakTermStructElim xts v' e')
substWeakTermPlus sub (m, WeakTermCase (e, t) cxtes) = do
  let e' = substWeakTermPlus sub e
  let t' = substWeakTermPlus sub t
  let cxtes' =
        flip map cxtes $ \((c, xts), body) -> do
          let (xts', body') = substWeakTermPlus'' sub xts body
          ((c, xts'), body')
  (m, WeakTermCase (e', t') cxtes')

-- substWeakTermPlus sub (m, WeakTermCocase as (name, es) ces) = do
--   let es' = map (substWeakTermPlus sub) es
--   let ces' =
--         flip map ces $ \(c, e) -> do
--           let e' = substWeakTermPlus sub e
--           (c, e')
--   (m, WeakTermCocase as (name, es') ces')
substWeakTermPlus' :: SubstWeakTerm -> [IdentifierPlus] -> [IdentifierPlus]
substWeakTermPlus' _ [] = []
substWeakTermPlus' sub ((m, x, t):xts) = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let xts' = substWeakTermPlus' sub' xts
  let t' = substWeakTermPlus sub t
  (m, x, t') : xts'

substWeakTermPlus'' ::
     SubstWeakTerm
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> ([IdentifierPlus], WeakTermPlus)
substWeakTermPlus'' sub [] e = do
  let e' = substWeakTermPlus sub e
  ([], e')
substWeakTermPlus'' sub ((m, x, t):xts) e = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let (xts', e') = substWeakTermPlus'' sub' xts e
  let t' = substWeakTermPlus sub t
  ((m, x, t') : xts', e')

metaOf :: WeakTermPlus -> Meta
metaOf e = fst e

asUpsilon :: WeakTermPlus -> Maybe Identifier
asUpsilon (_, WeakTermUpsilon x) = Just x
asUpsilon _ = Nothing

asUniv :: UnivLevelPlus -> WeakTermPlus
asUniv (UnivLevelPlus (m, l)) = (m, WeakTermTau l)

unit :: WeakTermPlus
unit = (emptyMeta, WeakTermEnumIntro $ EnumValueLabel "unit")

toText :: WeakTermPlus -> T.Text
toText (_, WeakTermTau l) = showCons ["tau", T.pack $ show l]
toText (_, WeakTermUpsilon x) = asText' x
toText (_, WeakTermPi _ xts t) = do
  let argStr = inParen $ showItems $ map showArg xts
  showCons ["Π", argStr, toText t]
toText (_, WeakTermPiPlus name _ _ _) = name -- Pi{nat} (...). (...) ~> nat
toText (_, WeakTermPiIntro xts e) = do
  let argStr = inParen $ showItems $ map showArg xts
  showCons ["λ", argStr, toText e]
toText (_, WeakTermPiIntroPlus name _ _ _ _) = do
  "<#" <> name <> "-" <> "value" <> "#>" -- <#succ-value#>, <#cons-value#>, <#nil-value#>, etc.
toText (_, WeakTermPiElim e es) = do
  showCons $ map toText $ e : es
toText (_, WeakTermSigma xts)
  | Just (yts, (_, _, t)) <- splitLast xts = do
    let argStr = inParen $ showItems $ map showArg yts
    showCons ["Σ", argStr, toText t]
  | otherwise = "(product)" -- <> : (product)
toText (_, WeakTermSigmaIntro _ es) = do
  showCons ("sigma-introduction" : map toText es)
  -- showTuple $ map toText es
toText (_, WeakTermSigmaElim _ xts e1 e2) = do
  let argStr = inParen $ showItems $ map showArg xts
  showCons ["sigma-elimination", argStr, toText e1, toText e2]
toText (_, WeakTermIter (_, x, _) xts e) = do
  let argStr = inParen $ showItems $ map showArg xts
  showCons ["μ", asText' x, argStr, toText e]
toText (_, WeakTermConst x) = asText' x
toText (_, WeakTermZeta x) = asText' x
toText (_, WeakTermInt _ a) = T.pack $ show a
toText (_, WeakTermFloat16 a) = T.pack $ show a
toText (_, WeakTermFloat32 a) = T.pack $ show a
toText (_, WeakTermFloat64 a) = T.pack $ show a
toText (_, WeakTermFloat _ a) = T.pack $ show a
toText (_, WeakTermEnum enumType) =
  case enumType of
    EnumTypeLabel l -> l
    EnumTypeIntS size -> "i" <> T.pack (show size)
    EnumTypeIntU size -> "u" <> T.pack (show size)
    -- EnumTypeNat size -> "n" <> T.pack (show size)
toText (_, WeakTermEnumIntro v) = showEnumValue v
toText (_, WeakTermEnumElim (e, _) les) =
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
  let argStr = inParen $ showItems $ map (\(_, x, _) -> asText' x) xts
  showCons ["struct-elimination", argStr, toText e1, toText e2]
toText (_, WeakTermCase (e, _) cxtes) = do
  showCons
    ("case" :
     toText e :
     (flip map cxtes $ \((c, xts), body) -> do
        let xs = map (\(_, I (x, _), _) -> x) xts
        showCons [showCons (asText c : xs), toText body]))

-- toText (_, WeakTermCocase _ (name, es) ces) = do
--   showCons
--     ("cocase" :
--      showCons (asText name : map toText es) :
--      (flip map ces $ \(c, e) -> showCons [asText c, toText e]))
inParen :: T.Text -> T.Text
inParen s = "(" <> s <> ")"

inAngle :: T.Text -> T.Text
inAngle s = "<" <> s <> ">"

inBrace :: T.Text -> T.Text
inBrace s = "{" <> s <> "}"

inBracket :: T.Text -> T.Text
inBracket s = "[" <> s <> "]"

showArg :: (Meta, Identifier, WeakTermPlus) -> T.Text
showArg (_, x, t) = inParen $ asText' x <> " " <> toText t

showClause :: (WeakCase, WeakTermPlus) -> T.Text
showClause (c, e) = inParen $ showWeakCase c <> " " <> toText e

showWeakCase :: WeakCase -> T.Text
showWeakCase (WeakCaseLabel l) = l
showWeakCase (WeakCaseIntS _ a) = T.pack $ show a
showWeakCase (WeakCaseIntU _ a) = T.pack $ show a
showWeakCase (WeakCaseInt _ a) = T.pack $ show a
-- showWeakCase (WeakCaseNat size a) = T.pack $ "n" ++ show size ++ "-" ++ show a
showWeakCase WeakCaseDefault = "default"

weakenEnumValue :: EnumValue -> WeakCase
weakenEnumValue (EnumValueLabel l) = WeakCaseLabel l
weakenEnumValue (EnumValueIntS t a) = WeakCaseIntS t a
weakenEnumValue (EnumValueIntU t a) = WeakCaseIntU t a

-- weakenEnumValue (EnumValueNat size a) = WeakCaseNat size a
weakenCase :: Case -> WeakCase
weakenCase (CaseValue v) = weakenEnumValue v
weakenCase CaseDefault = WeakCaseDefault

showEnumValue :: EnumValue -> T.Text
showEnumValue (EnumValueLabel l) = l
showEnumValue (EnumValueIntS _ a) = T.pack $ show a
showEnumValue (EnumValueIntU _ a) = T.pack $ show a

-- showEnumValue (EnumValueNat size a) = T.pack $ "n" ++ show size ++ "-" ++ show a
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
