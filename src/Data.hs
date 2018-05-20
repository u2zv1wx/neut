module Data where

data Symbol
  = S String
  | Hole
  deriving (Show)

-- positive symbol
-- x+ ::= symbol+
--      | (ascribe x+ P)
--      | [ascribe x+ P]
data PosSym
  = PosSym Symbol
  | PosSymAsc PosSym
              PosType
  deriving (Show)

-- negative symbol
-- x- ::= symbol-
--      | (ascribe x- N)
--      | [ascribe x- N]
data NegSym
  = NegSym Symbol
  | NegSymAsc NegSym
              NegType
  deriving (Show)

-- type
-- T ::= P
--     | N
--     | (universe i)
data Type
  = PosType PosType
  | NegType NegType
  deriving (Show)

-- positive type
-- P ::= p
--     | {defined value}
--     | {inverted form of defined computation}
--     | [forall ((x1- N1) ... (xn- Nn)) P]
--     | [switch x- N (r1 P1) ... (rn Pn)]
--     | [branch N P]
--     | (closure N)
--     | positive
data PosType
  = PosTypeSym PosSym
  | ValueApp ValueType
             [Type]
  | InvCompApp CompType
               [Type]
  | CoForAll [NegSym]
             NegType
             PosType
  | CoForAllPat NegSym
                NegType
                [(Refutation, PosType)]
  | Closure NegType
  | PosUniv Int
  deriving (Show)

-- negative type
-- N ::= n
--     | {defined computation type}
--     | {inverted form of defined value}
--     | (forall ((x1+ P1) ... (xn+ Pn)) N)
--     | (switch x+ P (a1 N1) ... (an Nn))
--     | (branch P N)
--     | [closure P]
--     | [N T1 ... Tn]
--     | negative
data NegType
  = NegTypeSym
  | CompApp CompType
            [Type]
  | InvValueApp ValueType
                [Type]
  | ForAll [PosSym]
           PosType
           NegType
  | Switch PosSym
           PosType
           [(Assertion, NegType)]
  | CoClosure PosType
  | NegUniv Int
  deriving (Show)

-- program
-- z ::= (thread t1) ... (thread tn)
newtype Program =
  Thread [Term]
  deriving (Show)

-- term
-- t ::= v | e
data Term
  = PosTerm V
  | NegTerm E
  deriving (Show)

-- positive term
-- v ::= x
--     | {pattern}
--     | {pattern application}
--     | [lambda [x1 ... xn] v]
--     | [v e1 ... en]
--     | [zeta x (r1 v1) ... (rn vn)]
--     | [elim e v]
--     | (thunk e)
--     | [force e]
--     | (quote e)
--     | [unquote e]
--     | (ascribe v P)
--     | [ascribe v P]
data V
  = VPosSym PosSym
  | VConsApp Constructor
             [Term]
  | CoLam [NegSym]
          V
  | CoApp V
          [E]
  | CoZeta NegSym
           [(Refutation, V)]
  | CoAppZeta E
              V
  | Thunk E
  | CoForce E
  | CoAsc V
          PosType
  deriving (Show)

-- negative term
-- e ::= x
--     | {pattern}
--     | (lambda (x1 ... xn) e)
--     | (e v1 ... vn)
--     | (zeta x (a1 e1) ... (an en))
--     | (elim v e)
--     | [thunk v]
--     | (force v)
--     | [quote v]
--     | (unquote v)
--     | (ascribe e N)
--     | [ascribe e N]
data E
  = ENegSym NegSym
  | EConsApp Constructor
             [Term]
  | Lam [PosSym]
        E
  | App E
        [V]
  | Zeta PosSym
         [(Assertion, E)]
  | AppZeta V
            E
  | CoThunk V
  | Force V
  | Asc E
        NegType
  deriving (Show)

-- constructor
data Cons a =
  Make Symbol
       [a]
  deriving (Show)

-- pattern ::= a | r
data Pat
  = PosPat Assertion
  | NegPat Refutation
  deriving (Show)

-- assertion pattern
-- a ::= x
--     | [return r]
--     | {etc.}
data Assertion
  = PosAtom PosSym
  | PosConsApp Constructor
               [Pat]
  deriving (Show)

-- refutation pattern
-- r ::= x
--     | (return a)
--     | {etc.}
data Refutation
  = NegAtom NegSym
  | NegConsApp Constructor
               [Pat]
  deriving (Show)

inclusionA :: Assertion -> V
inclusionA (PosAtom s) = VPosSym s
inclusionA (PosConsApp c args) = VConsApp c (map inclusionPat args)

inclusionR :: Refutation -> E
inclusionR (NegAtom s) = ENegSym s
inclusionR (NegConsApp c args) = EConsApp c (map inclusionPat args)

inclusionPat :: Pat -> Term
inclusionPat (PosPat a) = PosTerm (inclusionA a)
inclusionPat (NegPat r) = NegTerm (inclusionR r)

data TypeSpec = TypeSpec
  { specName :: Symbol
  , specArg :: [(Symbol, Type)]
  } deriving (Show)

-- value-type definition
-- valuedef ::= (value s (x1 t1) ... (xn tn))
newtype ValueType =
  ValueType TypeSpec
  deriving (Show)

-- computation-type definition
-- compdef ::= (computation s (x1 t1) ... (xn tn))
newtype CompType =
  CompType TypeSpec
  deriving (Show)

-- constructor definition
-- consdef ::= (constructor s (x1 t1) ... (xn tn) t)
data Constructor = Constructor
  { name :: Symbol
  , arg :: [(Symbol, Type)]
  , cod :: Type
  } deriving (Show)

data Env = Env
  { i :: Int
  , valueTypeEnv :: [ValueType]
  , compTypeEnv :: [CompType]
  , consEnv :: [Constructor]
  } deriving (Show)
