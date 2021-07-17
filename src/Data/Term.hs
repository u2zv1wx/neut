module Data.Term where

import Control.Exception.Safe
import Data.Basic
import qualified Data.IntMap as IntMap
import Data.Log
import Data.LowType
import qualified Data.Text as T
import Data.WeakTerm
import Path

data Term
  = TermTau
  | TermVar VarKind Ident
  | TermPi [IdentPlus] TermPlus
  | TermPiIntro Opacity (LamKind IdentPlus) [IdentPlus] TermPlus
  | TermPiElim TermPlus [TermPlus]
  | TermConst T.Text
  | TermInt IntSize Integer
  | TermFloat FloatSize Double
  | TermEnum (Path Abs File) T.Text
  | TermEnumIntro (Path Abs File) T.Text
  | TermEnumElim (TermPlus, TermPlus) [(EnumCasePlus, TermPlus)]
  | TermDerangement Derangement [TermPlus]
  | TermCase
      TermPlus -- result type
      (Maybe TermPlus) -- noetic subject (this is for `case-noetic`)
      (TermPlus, TermPlus) -- (pattern-matched value, its type)
      [(Pattern, TermPlus)]
  | TermIgnore TermPlus
  deriving (Show)

type Pattern =
  (Hint, Ident, [IdentPlus])

type TermPlus =
  (Hint, Term)

type SubstTerm =
  IntMap.IntMap TermPlus

type IdentPlus =
  (Hint, Ident, TermPlus)

type TypeEnv =
  IntMap.IntMap TermPlus

type StmtPlus =
  (Path Abs File, [Stmt])

data Stmt
  = StmtDef Hint Ident TermPlus TermPlus
  deriving (Show)

asVar :: TermPlus -> Maybe Ident
asVar term =
  case term of
    (_, TermVar _ x) ->
      Just x
    _ ->
      Nothing

weaken :: TermPlus -> WeakTermPlus
weaken term =
  case term of
    (m, TermTau) ->
      (m, WeakTermTau)
    (m, TermVar kind x) ->
      (m, WeakTermVar kind x)
    (m, TermPi xts t) ->
      (m, WeakTermPi (map weakenIdentPlus xts) (weaken t))
    (m, TermPiIntro opacity kind xts e) -> do
      let kind' = weakenKind kind
      let xts' = map weakenIdentPlus xts
      let e' = weaken e
      (m, WeakTermPiIntro opacity kind' xts' e')
    (m, TermPiElim e es) -> do
      let e' = weaken e
      let es' = map weaken es
      (m, WeakTermPiElim e' es')
    (m, TermConst x) ->
      (m, WeakTermConst x)
    (m, TermInt size x) ->
      (m, WeakTermInt (m, WeakTermConst (showIntSize size)) x)
    (m, TermFloat size x) ->
      (m, WeakTermFloat (m, WeakTermConst (showFloatSize size)) x)
    (m, TermEnum filePath x) ->
      (m, WeakTermEnum filePath x)
    (m, TermEnumIntro filePath l) ->
      (m, WeakTermEnumIntro filePath l)
    (m, TermEnumElim (e, t) branchList) -> do
      let t' = weaken t
      let e' = weaken e
      let (caseList, es) = unzip branchList
      let caseList' = map (\(me, ec) -> (me, weakenEnumCase ec)) caseList
      let es' = map weaken es
      (m, WeakTermEnumElim (e', t') (zip caseList' es'))
    (m, TermDerangement i es) -> do
      let es' = map weaken es
      (m, WeakTermDerangement i es')
    (m, TermCase resultType mSubject (e, t) patList) -> do
      let resultType' = weaken resultType
      let mSubject' = fmap weaken mSubject
      let e' = weaken e
      let t' = weaken t
      let patList' = map (\((mp, p, xts), body) -> ((mp, p, map weakenIdentPlus xts), weaken body)) patList
      (m, WeakTermCase resultType' mSubject' (e', t') patList')
    (m, TermIgnore e) ->
      (m, WeakTermIgnore (weaken e))

weakenEnumCase :: EnumCase -> WeakEnumCase
weakenEnumCase ec =
  case ec of
    EnumCaseLabel fp l ->
      WeakEnumCaseLabel (Just fp) l
    EnumCaseInt i ->
      WeakEnumCaseInt i
    EnumCaseDefault ->
      WeakEnumCaseDefault

weakenIdentPlus :: (Hint, Ident, TermPlus) -> (Hint, Ident, WeakTermPlus)
weakenIdentPlus (m, x, t) =
  (m, x, weaken t)

weakenKind :: LamKind IdentPlus -> LamKind WeakIdentPlus
weakenKind kind =
  case kind of
    LamKindNormal ->
      LamKindNormal
    LamKindCons t1 t2 ->
      LamKindCons t1 t2
    LamKindFix xt ->
      LamKindFix (weakenIdentPlus xt)
    LamKindResourceHandler ->
      LamKindResourceHandler

lowTypeToType :: (MonadThrow m) => Hint -> LowType -> m TermPlus
lowTypeToType m lowType =
  case lowType of
    LowTypeInt s ->
      return (m, TermConst (showIntSize s))
    LowTypeFloat s ->
      return (m, TermConst (showFloatSize s))
    _ ->
      raiseCritical m "invalid argument passed to lowTypeToType"
