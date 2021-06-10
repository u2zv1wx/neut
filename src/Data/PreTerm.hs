module Data.PreTerm where

import Data.Basic
import qualified Data.IntMap as IntMap
import Data.LowType
import qualified Data.Text as T

data PreTerm
  = PreTermSymbol T.Text
  | PreTermString T.Text
  | PreTermPi [PreIdentPlus] PreTermPlus
  | PreTermPiIntro [PreIdentPlus] PreTermPlus
  | PreTermPiElim PreTermPlus [PreTermPlus]
  | PreTermEnumElim PreTermPlus [(T.Text, PreTermPlus)]
  | PreTermQuestion PreTermPlus -- e : t (output the type `t` as note)
  | PreTermDerangement Derangement [PreTermPlus] -- (derangement kind arg-1 ... arg-n)
  | PreTermCase IsNoetic PreTermPlus [(PrePattern, PreTermPlus)]
  | PreTermCocase T.Text [(T.Text, PreTermPlus)]
  | PreTermLet T.Text PreTermPlus PreTermPlus
  | PreTermLetCoproduct T.Text PreTermPlus PreTermPlus
  | PreTermIf PreTermPlus PreTermPlus PreTermPlus
  deriving (Show)

type IsNoetic = Bool

type IsCoproduct = Bool

type PreTermPlus =
  (Hint, PreTerm)

type PrePattern =
  (Hint, T.Text, [T.Text])

type SubstPreTerm =
  IntMap.IntMap PreTermPlus

type PreIdentPlus =
  (Hint, T.Text, PreTermPlus)

type PreTextPlus =
  (Hint, T.Text, PreTermPlus)
