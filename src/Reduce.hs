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
reduce (i :< NeutPi (x, tdom) tcod) = do
  tdom' <- reduce tdom
  tcod' <- reduce tcod
  return $ i :< NeutPi (x, tdom') tcod'
reduce (i :< NeutPiElim e1 e2) = do
  e2' <- reduce e2
  e1' <- reduce e1
  case e1' of
    _ :< NeutPiIntro (arg, _) body -> do
      let sub = [(arg, e2')]
      let _ :< body' = subst sub body
      reduce $ i :< body'
    _ -> return $ i :< NeutPiElim e1' e2'
reduce (i :< NeutSigma xts t) = do
  let (xs, ts) = unzip xts
  ts' <- mapM reduce ts
  t' <- reduce t
  return $ i :< NeutSigma (zip xs ts') t'
reduce (i :< NeutSigmaIntro es) = do
  es' <- mapM reduce es
  return $ i :< NeutSigmaIntro es'
reduce (i :< NeutSigmaElim e xs body) = do
  e' <- reduce e
  case e of
    _ :< NeutSigmaIntro es -> do
      let _ :< body' = subst (zip xs es) body
      reduce $ i :< body'
    _ -> return $ i :< NeutSigmaElim e' xs body
reduce (i :< NeutBox t) = do
  t' <- reduce t
  return $ i :< NeutBox t'
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
        Just body -> reduce body
        Nothing ->
          case findLabelIndex branchList of
            Just (y, body) -> reduce $ subst [(y, e')] body
            Nothing ->
              case findDefault branchList of
                Just body -> reduce body
                Nothing ->
                  lift $
                  throwE $
                  "the index " ++ show x ++ " is not included in branchList"
    _ -> return $ i :< NeutIndexElim e' branchList
reduce (meta :< NeutMu s e) = do
  boxMeta <- newNameWith "meta"
  let box = boxMeta :< NeutBoxIntro (meta :< NeutMu s e)
  reduce $ subst [(s, box)] e
reduce (i :< NeutConst t) = do
  t' <- reduce t
  return $ i :< NeutConst t'
reduce (i :< NeutConstElim e) = do
  e' <- reduce e
  case e' of
    _ :< NeutConstIntro x -> do
      return $ i :< NeutConstElim e'
    _ -> return $ i :< NeutConstElim e'
reduce t = return t

findLabelIndex :: [(Index, Neut)] -> Maybe (Identifier, Neut)
findLabelIndex [] = Nothing
findLabelIndex ((l, e):ls) =
  case getLabelIndex l of
    Just i -> Just (i, e)
    Nothing -> findLabelIndex ls

getLabelIndex :: Index -> Maybe Identifier
getLabelIndex (IndexLabel x) = Just x
getLabelIndex _ = Nothing

findDefault :: [(Index, Neut)] -> Maybe Neut
findDefault [] = Nothing
findDefault ((IndexDefault, e):_) = Just e
findDefault (_:rest) = findDefault rest

isNonRecReducible :: Neut -> Bool
isNonRecReducible (_ :< NeutVar _) = False
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
isNonRecReducible (_ :< NeutConst _) = False
isNonRecReducible (_ :< NeutConstIntro _) = False
isNonRecReducible (_ :< NeutConstElim _) = False
isNonRecReducible (_ :< NeutMu _ _) = False
isNonRecReducible (_ :< NeutHole _) = False

nonRecReduce :: Neut -> WithEnv Neut
nonRecReduce e@(_ :< NeutVar _) = return e
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
nonRecReduce e@(_ :< NeutConst _) = return e
nonRecReduce e@(_ :< NeutConstIntro _) = return e
nonRecReduce e@(_ :< NeutConstElim _) = return e
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
    _ -> do
      let (labelList, es) = unzip branchList
      es' <- mapM reduceNeg es
      return $ NegIndexElim e $ zip labelList es'
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
reduceNeg (NegConstElim e) = do
  e' <- reducePos e
  case e' of
    PosConstIntro x -> return $ NegConstElim $ PosConstIntro x
    _ -> return $ NegConstElim e'
reduceNeg (NegPrint x e) = do
  e' <- reducePos e
  return $ NegPrint x e'
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
reduceComp (CompPiElimConstElim x xs) = return $ CompPiElimConstElim x xs
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
    _ -> do
      let (labelList, es) = unzip branchList
      es' <- mapM reduceComp es
      return $ CompIndexElim e $ zip labelList es'
reduceComp (CompUpIntro e) = do
  e' <- reduceValue e
  return $ CompUpIntro e'
reduceComp (CompUpElim x e1 e2) = do
  e1' <- reduceComp e1
  e2' <- reduceComp e2
  case e1' of
    CompUpIntro (ValueVar y) -> reduceComp $ substComp [(x, y)] e2'
    -- CompUpIntro (ValueConstIntro y) -> reduceComp $ substComp [(x, y)] e2'
    _ -> return $ CompUpElim x e1' e2'
reduceComp (CompPrint t e) = do
  e' <- reduceValue e
  return $ CompPrint t e'

subst :: Subst -> Neut -> Neut
subst sub (j :< NeutVar s) = fromMaybe (j :< NeutVar s) (lookup s sub)
subst sub (j :< NeutPi (s, tdom) tcod) = do
  let tdom' = subst sub tdom
  let sub' = filter (\(x, _) -> x /= s) sub
  let tcod' = subst sub' tcod
  j :< NeutPi (s, tdom') tcod'
subst sub (j :< NeutPiIntro (s, tdom) body) = do
  let tdom' = subst sub tdom
  let sub' = filter (\(x, _) -> x /= s) sub
  let body' = subst sub' body
  j :< NeutPiIntro (s, tdom') body'
subst sub (j :< NeutPiElim e1 e2) = do
  let e1' = subst sub e1
  let e2' = subst sub e2
  j :< NeutPiElim e1' e2'
subst sub (j :< NeutSigma xts t) = do
  let (xts', t') = substSigma sub xts t
  j :< NeutSigma xts' t'
subst sub (j :< NeutSigmaIntro es) = j :< NeutSigmaIntro (map (subst sub) es)
subst sub (j :< NeutSigmaElim e1 xs e2) = do
  let e1' = subst sub e1
  let sub' = filter (\(x, _) -> x `notElem` xs) sub
  let e2' = subst sub' e2
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
  let branchList' =
        flip map branchList $ \(l, e) -> do
          let vs = varIndex l
          let sub' = filter (\(x, _) -> x `notElem` vs) sub
          (l, subst sub' e)
  j :< NeutIndexElim e' branchList'
subst sub (j :< NeutConst t) = j :< NeutConst (subst sub t)
subst _ (j :< NeutConstIntro s) = j :< NeutConstIntro s
subst sub (j :< NeutConstElim e) = j :< NeutConstElim (subst sub e)
subst _ (j :< NeutUniv i) = j :< NeutUniv i
subst sub (j :< NeutMu x e) = do
  let sub' = filter (\(y, _) -> x /= y) sub
  let e' = subst sub' e
  j :< NeutMu x e'
subst sub (j :< NeutHole s) = fromMaybe (j :< NeutHole s) (lookup s sub)

substSigma ::
     Subst -> [(Identifier, Neut)] -> Neut -> ([(Identifier, Neut)], Neut)
substSigma sub [] e = ([], subst sub e)
substSigma sub ((x, t):rest) e = do
  let sub' = filter (\(y, _) -> y /= x) sub
  let (xts, e') = substSigma sub' rest e
  let t' = subst sub t
  ((x, t') : xts, e')

varIndex :: Index -> [Identifier]
varIndex (IndexLabel x) = [x]
varIndex _ = []

type SubstPos = [(Identifier, Pos)]

substPos :: SubstPos -> Pos -> Pos
substPos sub (PosVar s) = fromMaybe (PosVar s) (lookup s sub)
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
substPos sub (PosConst s) = PosConst $ substPos sub s
substPos _ (PosConstIntro x) = PosConstIntro x
substPos sub (PosArith kind e1 e2) = do
  let e1' = substPos sub e1
  let e2' = substPos sub e2
  PosArith kind e1' e2'

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
substNeg sub (NegConstElim e) = NegConstElim $ substPos sub e
substNeg sub (NegPrint x e) = NegPrint x (substPos sub e)
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
substValue _ (ValueConstIntro x) = ValueConstIntro x
substValue sub (ValueArith kind e1 e2) = do
  let e1' = substValue sub e1
  let e2' = substValue sub e2
  ValueArith kind e1' e2'

substComp :: SubstValue -> Comp -> Comp
substComp sub (CompPi (s, tdom) tcod) = do
  let tdom' = substValue sub tdom
  let tcod' = substComp sub tcod
  CompPi (s, tdom') tcod'
substComp sub (CompPiElimConstElim x xs) = do
  let x' = fromMaybe x (lookup x sub)
  let xs' = map (\y -> fromMaybe y (lookup y sub)) xs
  CompPiElimConstElim x' xs'
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

reduceTerm :: Term -> WithEnv Term
reduceTerm (TermPiElim e1 e2) = do
  e2' <- reduceTerm e2
  e1' <- reduceTerm e1
  case e1' of
    TermPiIntro arg body -> do
      let sub = [(arg, e2')]
      let body' = substTerm sub body
      reduceTerm body'
    _ -> return $ TermPiElim e1' e2'
reduceTerm (TermSigmaIntro es) = do
  es' <- mapM reduceTerm es
  return $ TermSigmaIntro es'
reduceTerm (TermSigmaElim e xs body) = do
  e' <- reduceTerm e
  case e of
    TermSigmaIntro es -> do
      es' <- mapM reduceTerm es
      let body' = substTerm (zip xs es') body
      reduceTerm body'
    _ -> return $ TermSigmaElim e' xs body
reduceTerm (TermBoxElim e) = do
  e' <- reduceTerm e
  case e' of
    TermBoxIntro e'' -> reduceTerm e''
    _ -> return $ TermBoxElim e'
reduceTerm (TermIndexElim e branchList) = do
  e' <- reduceTerm e
  case e' of
    TermIndexIntro x _ ->
      case lookup x branchList of
        Nothing ->
          lift $
          throwE $ "the index " ++ show x ++ " is not included in branchList"
        Just body -> reduceTerm body
    _ -> return $ TermIndexElim e' branchList
reduceTerm (TermMu s e) = do
  e' <- reduceTerm e
  return $ TermMu s e'
reduceTerm t = return t

type SubstTerm = [(Identifier, Term)]

substTerm :: SubstTerm -> Term -> Term
substTerm sub (TermVar s) = fromMaybe (TermVar s) (lookup s sub)
substTerm sub (TermPi (s, tdom) tcod) = do
  let tdom' = substTerm sub tdom
  let tcod' = substTerm sub tcod
  TermPi (s, tdom') tcod'
substTerm sub (TermPiIntro s body) = do
  let body' = substTerm sub body
  TermPiIntro s body'
substTerm sub (TermPiElim e1 e2) = do
  let e1' = substTerm sub e1
  let e2' = substTerm sub e2
  TermPiElim e1' e2'
substTerm sub (TermSigma xts tcod) = do
  let (xs, ts) = unzip xts
  let ts' = map (substTerm sub) ts
  let tcod' = substTerm sub tcod
  TermSigma (zip xs ts') tcod'
substTerm sub (TermSigmaIntro es) = TermSigmaIntro (map (substTerm sub) es)
substTerm sub (TermSigmaElim e1 xs e2) = do
  let e1' = substTerm sub e1
  let e2' = substTerm sub e2
  TermSigmaElim e1' xs e2'
substTerm sub (TermBox e) = do
  let e' = substTerm sub e
  TermBox e'
substTerm sub (TermBoxIntro e) = do
  let e' = substTerm sub e
  TermBoxIntro e'
substTerm sub (TermBoxElim e) = do
  let e' = substTerm sub e
  TermBoxElim e'
substTerm _ (TermIndex x) = TermIndex x
substTerm _ (TermIndexIntro l meta) = TermIndexIntro l meta
substTerm sub (TermIndexElim e branchList) = do
  let e' = substTerm sub e
  let branchList' = map (\(l, e) -> (l, substTerm sub e)) branchList
  TermIndexElim e' branchList'
substTerm sub (TermConst t) = TermConst (substTerm sub t)
substTerm _ (TermConstIntro s) = TermConstIntro s
substTerm sub (TermConstElim e) = TermConstElim (substTerm sub e)
substTerm _ (TermUniv i) = TermUniv i
substTerm sub (TermMu x e) = do
  let e' = substTerm sub e
  TermMu x e'
