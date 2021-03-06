module Data.Term where

import Control.Exception.Safe
import Data.Basic
import qualified Data.IntMap as IntMap
import Data.Log
import Data.LowType
import qualified Data.Set as S
import qualified Data.Text as T
import Data.WeakTerm

data Term
  = TermTau
  | TermUpsilon Ident
  | TermPi [IdentPlus] TermPlus
  | TermPiIntro [IdentPlus] TermPlus
  | TermPiElim TermPlus [TermPlus]
  | TermFix IdentPlus [IdentPlus] TermPlus
  | TermConst T.Text
  | TermInt IntSize Integer
  | TermFloat FloatSize Double
  | TermEnum T.Text
  | TermEnumIntro T.Text
  | TermEnumElim (TermPlus, TermPlus) [(EnumCasePlus, TermPlus)]
  | TermTensor [TermPlus]
  | TermTensorIntro [TermPlus]
  | TermTensorElim [IdentPlus] TermPlus TermPlus
  | TermDerangement Derangement TermPlus [(TermPlus, DerangementArg, TermPlus)]
  deriving (Show)

type TermPlus =
  (Hint, Term)

type SubstTerm =
  IntMap.IntMap TermPlus

type IdentPlus =
  (Hint, Ident, TermPlus)

type TypeEnv =
  IntMap.IntMap TermPlus

data Stmt
  = StmtLet Hint IdentPlus TermPlus
  | StmtResourceType Hint T.Text TermPlus TermPlus
  deriving (Show)

asUpsilon :: TermPlus -> Maybe Ident
asUpsilon term =
  case term of
    (_, TermUpsilon x) ->
      Just x
    _ ->
      Nothing

varTermPlus :: TermPlus -> S.Set Ident
varTermPlus term =
  case term of
    (_, TermTau) ->
      S.empty
    (_, TermUpsilon x) ->
      S.singleton x
    (_, TermPi xts t) ->
      varTermPlus' xts [t]
    (_, TermPiIntro xts e) ->
      varTermPlus' xts [e]
    (_, TermPiElim e es) -> do
      let xs1 = varTermPlus e
      let xs2 = S.unions $ map varTermPlus es
      S.union xs1 xs2
    (_, TermFix (_, x, t) xts e) -> do
      let set1 = varTermPlus t
      let set2 = S.filter (/= x) (varTermPlus' xts [e])
      S.union set1 set2
    (_, TermConst _) ->
      S.empty
    (_, TermInt _ _) ->
      S.empty
    (_, TermFloat _ _) ->
      S.empty
    (_, TermEnum _) ->
      S.empty
    (_, TermEnumIntro _) ->
      S.empty
    (_, TermEnumElim (e, t) les) -> do
      let xs = varTermPlus t
      let ys = varTermPlus e
      let zs = S.unions $ map (varTermPlus . snd) les
      S.unions [xs, ys, zs]
    (_, TermTensor ts) ->
      S.unions $ map varTermPlus ts
    (_, TermTensorIntro es) ->
      S.unions $ map varTermPlus es
    (_, TermTensorElim xts e1 e2) -> do
      let xs = varTermPlus e1
      let ys = varTermPlus' xts [e2]
      S.unions [xs, ys]
    (_, TermDerangement _ _ ekts) -> do
      let (es, _, ts) = unzip3 ekts
      S.unions $ map varTermPlus (es ++ ts)

varTermPlus' :: [IdentPlus] -> [TermPlus] -> S.Set Ident
varTermPlus' binder es =
  case binder of
    [] ->
      S.unions $ map varTermPlus es
    ((_, x, t) : xts) -> do
      let set1 = varTermPlus t
      let set2 = varTermPlus' xts es
      S.union set1 $ S.filter (/= x) set2

weaken :: TermPlus -> WeakTermPlus
weaken term =
  case term of
    (m, TermTau) ->
      (m, WeakTermTau)
    (m, TermUpsilon x) ->
      (m, WeakTermUpsilon x)
    (m, TermPi xts t) ->
      (m, WeakTermPi (weakenArgs xts) (weaken t))
    (m, TermPiIntro xts body) -> do
      let xts' = weakenArgs xts
      (m, WeakTermPiIntro xts' (weaken body))
    (m, TermPiElim e es) -> do
      let e' = weaken e
      let es' = map weaken es
      (m, WeakTermPiElim e' es')
    (m, TermFix (mx, x, t) xts e) -> do
      let t' = weaken t
      let xts' = weakenArgs xts
      let e' = weaken e
      (m, WeakTermFix (mx, x, t') xts' e')
    (m, TermConst x) ->
      (m, WeakTermConst x)
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
    (m, TermTensor ts) -> do
      let ts' = map weaken ts
      (m, WeakTermTensor ts')
    (m, TermTensorIntro es) -> do
      let es' = map weaken es
      (m, WeakTermTensorIntro es')
    (m, TermTensorElim xts e1 e2) -> do
      let xts' = weakenArgs xts
      let e1' = weaken e1
      let e2' = weaken e2
      (m, WeakTermTensorElim xts' e1' e2')
    (m, TermDerangement i resultType ekts) -> do
      let (es, ks, ts) = unzip3 ekts
      let es' = map weaken es
      let ts' = map weaken ts
      let resultType' = weaken resultType
      (m, WeakTermDerangement i resultType' (zip3 es' ks ts'))

weakenArgs :: [(Hint, Ident, TermPlus)] -> [(Hint, Ident, WeakTermPlus)]
weakenArgs xts = do
  let (ms, xs, ts) = unzip3 xts
  zip3 ms xs (map weaken ts)

lowTypeToType :: (MonadThrow m) => Hint -> LowType -> m TermPlus
lowTypeToType m lowType =
  case lowType of
    LowTypeInt s ->
      return (m, TermEnum (showIntSize s))
    LowTypeFloat s ->
      return (m, TermConst (showFloatSize s))
    _ ->
      raiseCritical m "invalid argument passed to lowTypeToType"
