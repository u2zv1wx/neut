module Data where

newtype Symbol =
  S String
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
  | Univ Int
  deriving (Show)

-- positive type
-- P ::= p
--     | [lift N]
--     | [forall x- N P]
--     | [switch x- N (r1 P1) ... (rn Pn)]
--     | (closure N)
data PosType
  = PosTypeSym PosSym
  | CoLift NegType
  | CoForAll NegSym
             NegType
             PosType
  | CoForAllPat NegSym
                NegType
                [(Refutation, PosType)]
  | Closure NegType
  deriving (Show)

-- negative type
-- N ::= n
--     | (lift P)
--     | (forall x+ P N)
--     | (switch x+ P (a1 N1) ... (an Nn))
--     | [closure P]
data NegType
  = NegTypeSym
  | Lift PosType
  | ForAll PosSym
           PosType
           NegType
  | ForAllPat PosSym
              PosType
              [(Assertion, NegType)]
  | CoClosure PosType
  deriving (Show)

-- program
-- z ::= (thread t1) ... (thread tn)
newtype Program =
  Thread [Term]
  deriving (Show)

-- term
-- t ::= v | e
data Term
  = Value V
  | Expr E
  deriving (Show)

-- positive term
-- v ::= x
--     | {copattern}
--     | [lambda x v]
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
  | VPat (Cons Term)
  | CoLam NegSym
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
--     | (lambda x e)
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
  | EPat (Cons Term)
  | Lam PosSym
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
  = Assertion Assertion
  | Refutation Refutation
  deriving (Show)

-- assertion pattern
-- a ::= x
--     | [return r]
--     | {etc.}
data Assertion
  = PosAtom PosSym
  | PosCons (Cons Pat)
  deriving (Show)

-- refutation pattern
-- r ::= x
--     | (return a)
--     | {etc.}
data Refutation
  = NegAtom NegSym
  | NegCons (Cons Pat)
  deriving (Show)

inclusionA :: Assertion -> V
inclusionA (PosAtom s) = VPosSym s
inclusionA (PosCons (Make name args)) = VPat (Make name (map inclusionPat args))

inclusionR :: Refutation -> E
inclusionR (NegAtom s) = ENegSym s
inclusionR (NegCons (Make name args)) = EPat (Make name (map inclusionPat args))

inclusionPat :: Pat -> Term
inclusionPat (Assertion a) = Value (inclusionA a)
inclusionPat (Refutation r) = Expr (inclusionR r)
