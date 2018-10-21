module Reduce where

import Data

import Control.Comonad

import Control.Comonad.Cofree
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans.Except
import Text.Show.Deriving

import Data.Functor.Classes

import System.IO.Unsafe

import Data.IORef
import Data.List
import Data.Maybe (fromMaybe)
import Data.Tuple (swap)

import qualified Text.Show.Pretty as Pr

reduce :: Neut -> WithEnv Neut
reduce (i :< NeutPiElim e1 e2) = do
  e2' <- reduce e2
  e1' <- reduce e1
  case e1' of
    _ :< NeutPiIntro (arg, _) body -> do
      let sub = [(arg, e2')]
      let _ :< body' = subst sub body
      reduce $ i :< body'
    _ -> return $ i :< NeutPiElim e1' e2'
reduce (i :< NeutSigmaIntro es) = do
  es' <- mapM reduce es
  return $ i :< NeutSigmaIntro es'
reduce (i :< NeutSigmaElim e xs body) = do
  e' <- reduce e
  case e of
    _ :< NeutSigmaIntro es -> do
      es' <- mapM reduce es
      let _ :< body' = subst (zip xs es') body
      reduce $ i :< body'
    _ -> return $ i :< NeutSigmaElim e' xs body
reduce (i :< NeutBoxElim e) = do
  e' <- reduce e
  case e' of
    _ :< NeutBoxIntro e'' -> reduce e''
    _ -> return $ i :< NeutBoxElim e'
reduce (i :< NeutIndexElim e branchList) = do
  e' <- reduce e
  case e' of
    _ :< NeutIndexIntro x ->
      case lookup x branchList of
        Nothing ->
          lift $
          throwE $ "the index " ++ show x ++ " is not included in branchList"
        Just body -> reduce body
    _ -> return $ i :< NeutIndexElim e' branchList
reduce (meta :< NeutMu s e) = do
  e' <- reduce e
  return $ meta :< NeutMu s e'
reduce t = return t

isNonRecReducible :: Neut -> Bool
isNonRecReducible (_ :< NeutVar _) = False
isNonRecReducible (_ :< NeutConst _ _) = False
isNonRecReducible (_ :< NeutPi (_, tdom) tcod) =
  isNonRecReducible tdom || isNonRecReducible tcod
isNonRecReducible (_ :< NeutPiIntro _ e) = isNonRecReducible e
isNonRecReducible (_ :< NeutPiElim (_ :< NeutPiIntro _ _) _) = True
isNonRecReducible (_ :< NeutPiElim e1 e2) =
  isNonRecReducible e1 || isNonRecReducible e2
isNonRecReducible (_ :< NeutSigma xts tcod) =
  any isNonRecReducible $ tcod : map snd xts
isNonRecReducible (_ :< NeutSigmaIntro es) = any isNonRecReducible es
isNonRecReducible (_ :< NeutSigmaElim (_ :< NeutSigmaIntro _) _ _) = True
isNonRecReducible (_ :< NeutSigmaElim e _ body) =
  isNonRecReducible e || isNonRecReducible body
isNonRecReducible (_ :< NeutBox e) = isNonRecReducible e
isNonRecReducible (_ :< NeutBoxIntro e) = isNonRecReducible e
isNonRecReducible (_ :< NeutBoxElim (_ :< NeutBoxIntro _)) = True
isNonRecReducible (_ :< NeutBoxElim e) = isNonRecReducible e
isNonRecReducible (_ :< NeutIndex _) = False
isNonRecReducible (_ :< NeutIndexIntro _) = False
isNonRecReducible (_ :< NeutIndexElim (_ :< NeutIndexIntro _) _) = True
isNonRecReducible (_ :< NeutIndexElim e branchList) = do
  let es = map snd branchList
  any isNonRecReducible $ e : es
isNonRecReducible (_ :< NeutUniv _) = False
isNonRecReducible (_ :< NeutMu _ _) = False
isNonRecReducible (_ :< NeutHole _) = False

nonRecReduce :: Neut -> WithEnv Neut
nonRecReduce e@(_ :< NeutVar _) = return e
nonRecReduce e@(_ :< NeutConst _ _) = return e
nonRecReduce (i :< NeutPi (x, tdom) tcod) = do
  tdom' <- nonRecReduce tdom
  tcod' <- nonRecReduce tcod
  return $ i :< NeutPi (x, tdom') tcod'
nonRecReduce (i :< NeutPiIntro (x, tdom) e) = do
  e' <- nonRecReduce e
  return $ i :< NeutPiIntro (x, tdom) e'
nonRecReduce (i :< NeutPiElim e1 e2) = do
  e2' <- nonRecReduce e2
  e1' <- nonRecReduce e1
  case e1' of
    _ :< NeutPiIntro (arg, _) body -> do
      let sub = [(arg, e2')]
      let _ :< body' = subst sub body
      nonRecReduce $ i :< body'
    _ -> return $ i :< NeutPiElim e1' e2'
nonRecReduce (i :< NeutSigma xts tcod) = do
  let (xs, ts) = unzip xts
  ts' <- mapM nonRecReduce ts
  tcod' <- nonRecReduce tcod
  return $ i :< NeutSigma (zip xs ts') tcod'
nonRecReduce (i :< NeutSigmaIntro es) = do
  es' <- mapM nonRecReduce es
  return $ i :< NeutSigmaIntro es'
nonRecReduce (i :< NeutSigmaElim e xs body) = do
  e' <- nonRecReduce e
  case e' of
    _ :< NeutSigmaIntro es -> do
      es' <- mapM nonRecReduce es
      let sub = zip xs es'
      let _ :< body' = subst sub body
      reduce $ i :< body'
    _ -> return $ i :< NeutSigmaElim e' xs body
nonRecReduce (i :< NeutBox e) = do
  e' <- nonRecReduce e
  return $ i :< NeutBox e'
nonRecReduce (i :< NeutBoxIntro e) = do
  e' <- nonRecReduce e
  return $ i :< NeutBoxIntro e'
nonRecReduce (i :< NeutBoxElim e) = do
  e' <- nonRecReduce e
  case e' of
    _ :< NeutBoxIntro e'' -> nonRecReduce e''
    _ -> return $ i :< NeutBoxElim e'
nonRecReduce e@(_ :< NeutIndex _) = return e
nonRecReduce e@(_ :< NeutIndexIntro _) = return e
nonRecReduce (i :< NeutIndexElim e branchList) = do
  e' <- nonRecReduce e
  case e' of
    _ :< NeutIndexIntro x ->
      case lookup x branchList of
        Nothing ->
          lift $
          throwE $ "the index " ++ show x ++ " is not included in branchList"
        Just body -> nonRecReduce body
    _ -> return $ i :< NeutIndexElim e' branchList
nonRecReduce e@(_ :< NeutUniv _) = return e
nonRecReduce e@(_ :< NeutMu _ _) = return e
nonRecReduce e@(_ :< NeutHole x) = do
  sub <- gets substitution
  case lookup x sub of
    Just e' -> return e'
    Nothing -> return e

reducePos :: Pos -> WithEnv Pos
reducePos (PosDownIntro e) = do
  e' <- reduceNeg e
  return $ PosDownIntro e'
reducePos e = return e

reduceNeg :: Neg -> WithEnv Neg
reduceNeg (NegPi (x, tdom) tcod) = do
  tdom' <- reducePos tdom
  tcod' <- reduceNeg tcod
  return $ NegPi (x, tdom') tcod'
reduceNeg (NegPiIntro x e) = do
  e' <- reduceNeg e
  return $ NegPiIntro x e'
reduceNeg (NegPiElim e1 e2) = do
  e1' <- reduceNeg e1
  case e1' of
    NegPiIntro x body -> do
      let sub = [(x, e2)]
      let body' = substNeg sub body
      reduceNeg body'
    _ -> return $ NegPiElim e1' e2
reduceNeg (NegSigmaElim e xs body) =
  case e of
    PosSigmaIntro es -> do
      let sub = zip xs es
      let body' = substNeg sub body
      reduceNeg body'
    _ -> do
      body' <- reduceNeg body
      return $ NegSigmaElim e xs body'
reduceNeg (NegBoxElim e) = do
  e' <- reducePos e
  case e' of
    PosBoxIntro e'' -> reduceNeg e''
    _ -> return $ NegBoxElim e'
reduceNeg (NegIndexElim e branchList) =
  case e of
    PosIndexIntro x _ ->
      case lookup x branchList of
        Nothing ->
          lift $
          throwE $ "the index " ++ show x ++ " is not included in branchList"
        Just body -> reduceNeg body
    _ -> return $ NegIndexElim e branchList
reduceNeg (NegUpIntro e) = do
  e' <- reducePos e
  return $ NegUpIntro e'
reduceNeg (NegUpElim x e1 e2) = do
  e1' <- reduceNeg e1
  e2' <- reduceNeg e2
  case e1' of
    NegUpIntro e1'' -> reduceNeg $ substNeg [(x, e1'')] e2'
    _ -> return $ NegUpElim x e1' e2'
reduceNeg (NegDownElim e) = do
  e' <- reducePos e
  case e' of
    PosDownIntro e'' -> reduceNeg e''
    _ -> return $ NegDownElim e'
reduceNeg (NegMu x e) = do
  e' <- reduceNeg e
  return $ NegMu x e'

reduceValue :: Value -> WithEnv Value
reduceValue = return

reduceComp :: Comp -> WithEnv Comp
reduceComp (CompPi (x, tdom) tcod) = do
  tdom' <- reduceValue tdom
  tcod' <- reduceComp tcod
  return $ CompPi (x, tdom') tcod'
reduceComp (CompPiElimBoxElim x xs) = return $ CompPiElimBoxElim x xs
reduceComp (CompSigmaElim e xs body) = do
  body' <- reduceComp body
  return $ CompSigmaElim e xs body'
reduceComp (CompIndexElim e branchList) =
  case e of
    ValueIndexIntro x _ ->
      case lookup x branchList of
        Nothing ->
          lift $
          throwE $ "the index " ++ show x ++ " is not included in branchList"
        Just body -> reduceComp body
    _ -> return $ CompIndexElim e branchList
reduceComp (CompUpIntro e) = do
  e' <- reduceValue e
  return $ CompUpIntro e'
reduceComp (CompUpElim x e1 e2) = do
  e1' <- reduceComp e1
  e2' <- reduceComp e2
  case e1' of
    CompUpIntro (ValueVar y) -> reduceComp $ substComp [(x, y)] e2'
    CompUpIntro (ValueConst y) -> reduceComp $ substComp [(x, y)] e2'
    _ -> return $ CompUpElim x e1' e2'
reduceComp (CompPrint t e) = do
  e' <- reduceValue e
  return $ CompPrint t e'

subst :: Subst -> Neut -> Neut
subst sub (j :< NeutVar s) = fromMaybe (j :< NeutVar s) (lookup s sub)
subst sub (j :< NeutConst s t) = j :< NeutConst s (subst sub t)
subst sub (j :< NeutPi (s, tdom) tcod) = do
  let tdom' = subst sub tdom
  let tcod' = subst sub tcod -- note that we don't have to drop s from sub, thanks to rename.
  j :< NeutPi (s, tdom') tcod'
subst sub (j :< NeutPiIntro (s, tdom) body) = do
  let tdom' = subst sub tdom
  let body' = subst sub body
  j :< NeutPiIntro (s, tdom') body'
subst sub (j :< NeutPiElim e1 e2) = do
  let e1' = subst sub e1
  let e2' = subst sub e2
  j :< NeutPiElim e1' e2'
subst sub (j :< NeutSigma xts tcod) = do
  let (xs, ts) = unzip xts
  let ts' = map (subst sub) ts
  let tcod' = subst sub tcod
  j :< NeutSigma (zip xs ts') tcod'
subst sub (j :< NeutSigmaIntro es) = j :< NeutSigmaIntro (map (subst sub) es)
subst sub (j :< NeutSigmaElim e1 xs e2) = do
  let e1' = subst sub e1
  let e2' = subst sub e2
  j :< NeutSigmaElim e1' xs e2'
subst sub (j :< NeutBox e) = do
  let e' = subst sub e
  j :< NeutBox e'
subst sub (j :< NeutBoxIntro e) = do
  let e' = subst sub e
  j :< NeutBoxIntro e'
subst sub (j :< NeutBoxElim e) = do
  let e' = subst sub e
  j :< NeutBoxElim e'
subst _ (j :< NeutIndex x) = j :< NeutIndex x
subst _ (j :< NeutIndexIntro l) = j :< NeutIndexIntro l
subst sub (j :< NeutIndexElim e branchList) = do
  let e' = subst sub e
  let branchList' = map (\(l, e) -> (l, subst sub e)) branchList
  j :< NeutIndexElim e' branchList'
subst _ (j :< NeutUniv i) = j :< NeutUniv i
subst sub (j :< NeutMu x e) = do
  let e' = subst sub e
  j :< NeutMu x e'
subst sub (j :< NeutHole s) = fromMaybe (j :< NeutHole s) (lookup s sub)

type SubstPos = [(Identifier, Pos)]

substPos :: SubstPos -> Pos -> Pos
substPos sub (PosVar s) = fromMaybe (PosVar s) (lookup s sub)
substPos _ (PosConst s) = PosConst s
substPos sub (PosSigma xts tcod) = do
  let (xs, ts) = unzip xts
  let ts' = map (substPos sub) ts
  let tcod' = substPos sub tcod
  PosSigma (zip xs ts') tcod'
substPos sub (PosSigmaIntro es) = do
  let es' = map (substPos sub) es
  PosSigmaIntro es'
substPos sub (PosBox e) = do
  let e' = substNeg sub e
  PosBox e'
substPos sub (PosBoxIntro e) = do
  let e' = substNeg sub e
  PosBoxIntro e'
substPos _ (PosIndex x) = PosIndex x
substPos _ (PosIndexIntro l meta) = PosIndexIntro l meta
substPos _ PosUniv = PosUniv
substPos sub (PosDown e) = do
  let e' = substNeg sub e
  PosDown e'
substPos sub (PosDownIntro e) = do
  let e' = substNeg sub e
  PosDownIntro e'

substNeg :: SubstPos -> Neg -> Neg
substNeg sub (NegPi (s, tdom) tcod) = do
  let tdom' = substPos sub tdom
  let tcod' = substNeg sub tcod
  NegPi (s, tdom') tcod'
substNeg sub (NegPiIntro s body) = do
  let body' = substNeg sub body
  NegPiIntro s body'
substNeg sub (NegPiElim e1 e2) = do
  let e1' = substNeg sub e1
  let e2' = substPos sub e2
  NegPiElim e1' e2'
substNeg sub (NegSigmaElim e1 xs e2) = do
  let e1' = substPos sub e1
  let e2' = substNeg sub e2
  NegSigmaElim e1' xs e2'
substNeg sub (NegBoxElim e) = do
  let e' = substPos sub e
  NegBoxElim e'
substNeg sub (NegIndexElim e branchList) = do
  let e' = substPos sub e
  let branchList' = map (\(l, e) -> (l, substNeg sub e)) branchList
  NegIndexElim e' branchList'
substNeg sub (NegUpIntro e) = NegUpIntro (substPos sub e)
substNeg sub (NegUpElim x e1 e2) = do
  let e1' = substNeg sub e1
  let e2' = substNeg sub e2
  NegUpElim x e1' e2'
substNeg sub (NegDownElim e) = NegDownElim (substPos sub e)
substNeg sub (NegMu x e) = NegMu x $ substNeg sub e

type SubstValue = [(Identifier, Identifier)]

substValue :: SubstValue -> Value -> Value
substValue sub (ValueVar s) = do
  let s' = fromMaybe s (lookup s sub)
  ValueVar s'
substValue _ (ValueConst s) = ValueConst s
substValue sub (ValueSigma xts tcod) = do
  let (xs, ts) = unzip xts
  let ts' = map (substValue sub) ts
  let tcod' = substValue sub tcod
  ValueSigma (zip xs ts') tcod'
substValue sub (ValueSigmaIntro es) = do
  let es' = map (substValue sub) es
  ValueSigmaIntro es'
substValue sub (ValueBox e) = do
  let e' = substComp sub e
  ValueBox e'
substValue _ (ValueIndex x) = ValueIndex x
substValue _ (ValueIndexIntro l meta) = ValueIndexIntro l meta
substValue _ ValueUniv = ValueUniv
substValue sub (ValueArith kind e1 e2) = do
  let e1' = substValue sub e1
  let e2' = substValue sub e2
  ValueArith kind e1' e2'

substComp :: SubstValue -> Comp -> Comp
substComp sub (CompPi (s, tdom) tcod) = do
  let tdom' = substValue sub tdom
  let tcod' = substComp sub tcod
  CompPi (s, tdom') tcod'
substComp sub (CompPiElimBoxElim x xs) = do
  let x' = fromMaybe x (lookup x sub)
  let xs' = map (\y -> fromMaybe y (lookup y sub)) xs
  CompPiElimBoxElim x' xs'
  -- let e1' = substComp sub e1
  -- let e2' = substValue sub e2
  -- CompPiElim e1' e2'
substComp sub (CompSigmaElim e1 xs e2) = do
  let e1' = substValue sub e1
  let e2' = substComp sub e2
  CompSigmaElim e1' xs e2'
substComp sub (CompIndexElim e branchList) = do
  let e' = substValue sub e
  let branchList' = map (\(l, e) -> (l, substComp sub e)) branchList
  CompIndexElim e' branchList'
substComp sub (CompUpIntro e) = CompUpIntro (substValue sub e)
substComp sub (CompUpElim x e1 e2) = do
  let e1' = substComp sub e1
  let e2' = substComp sub e2
  CompUpElim x e1' e2'
substComp sub (CompPrint t e) = CompPrint t $ substValue sub e

-- findInvVar :: Subst -> Identifier -> Maybe Identifier
-- findInvVar [] _ = Nothing
-- findInvVar ((y, _ :< NeutVar x):rest) x'
--   | x == x' =
--     if not (any (/= y) $ findInvVar' rest x')
--       then Just y
--       else Nothing
-- findInvVar ((_, _):rest) i = findInvVar rest i
-- findInvVar' :: Subst -> Identifier -> [Identifier]
-- findInvVar' [] _ = []
-- findInvVar' ((z, _ :< NeutVar x):rest) x'
--   | x /= x' = z : findInvVar' rest x'
-- findInvVar' (_:rest) x' = findInvVar' rest x'
type SubstIdent = [(Identifier, Identifier)]

substIdent :: SubstIdent -> Identifier -> Identifier
substIdent sub x = fromMaybe x (lookup x sub)

compose :: Subst -> Subst -> Subst
compose s1 s2 = do
  let domS2 = map fst s2
  let codS2 = map snd s2
  let codS2' = map (subst s1) codS2
  let fromS1 = filter (\(ident, _) -> ident `notElem` domS2) s1
  fromS1 ++ zip domS2 codS2'
