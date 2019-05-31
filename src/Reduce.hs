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
reduce app@(i :< NeutPiElim _ _) = do
  let (fun, args) = toPiElimSeq app
  args' <-
    forM args $ \(x, e) -> do
      e' <- reduce e
      return (x, e')
  fun' <- reduce fun
  case fun' of
    lam@(_ :< NeutPiIntro _ _)
      | (body, xtms) <- toPiIntroSeq lam
      , length xtms == length args -> do
        let xs = map (\(x, _, _) -> x) xtms
        let es = map snd args'
        reduce $ subst (zip xs es) body
    _ ->
      case fun' of
        _ :< NeutConst constant
          | constant `elem` intAddConstantList
          , Just [x, y] <- takeIntegerList (map snd args') ->
            return $ i :< NeutIndexIntro (IndexInteger (x + y))
        _ :< NeutConst constant
          | constant `elem` intSubConstantList
          , Just [x, y] <- takeIntegerList (map snd args') ->
            return $ i :< NeutIndexIntro (IndexInteger (x - y))
        _ :< NeutConst constant
          | constant `elem` intMulConstantList
          , Just [x, y] <- takeIntegerList (map snd args') ->
            return $ i :< NeutIndexIntro (IndexInteger (x * y))
        _ :< NeutConst constant
          | constant `elem` intDivConstantList
          , Just [x, y] <- takeIntegerList (map snd args') ->
            return $ i :< NeutIndexIntro (IndexInteger (x `div` y))
        _ -> return $ fromPiElimSeq (fun', args')
reduce (i :< NeutSigmaElim e xs body) = do
  e' <- reduce e
  case e of
    _ :< NeutSigmaIntro es -> do
      let _ :< body' = subst (zip xs es) body
      reduce $ i :< body'
    _ -> return $ i :< NeutSigmaElim e' xs body
reduce (i :< NeutIndexElim e branchList) = do
  e' <- reduce e
  case e' of
    _ :< NeutIndexIntro x ->
      case lookup x branchList of
        Just body -> reduce body
        Nothing ->
          case findDefault branchList of
            Just body -> reduce body
            Nothing ->
              lift $
              throwE $
              "the index " ++ show x ++ " is not included in branchList"
    _ -> return $ i :< NeutIndexElim e' branchList
reduce (meta :< NeutMu s e) = reduce $ subst [(s, meta :< NeutMu s e)] e
reduce t = return t

subst :: Subst -> Neut -> Neut
subst sub (j :< NeutVar s) = fromMaybe (j :< NeutVar s) (lookup s sub)
subst _ (j :< NeutConst t) = j :< NeutConst t
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
subst sub (j :< NeutSigma xts) = j :< NeutSigma (substSigma sub xts)
subst sub (j :< NeutSigmaIntro es) = j :< NeutSigmaIntro (map (subst sub) es)
subst sub (j :< NeutSigmaElim e1 xs e2) = do
  let e1' = subst sub e1
  let sub' = filter (\(x, _) -> x `notElem` xs) sub
  let e2' = subst sub' e2
  j :< NeutSigmaElim e1' xs e2'
subst _ (j :< NeutIndex x) = j :< NeutIndex x
subst _ (j :< NeutIndexIntro l) = j :< NeutIndexIntro l
subst sub (j :< NeutIndexElim e branchList) = do
  let e' = subst sub e
  let branchList' = flip map branchList $ \(l, e) -> (l, subst sub e)
  j :< NeutIndexElim e' branchList'
subst _ (j :< NeutUniv i) = j :< NeutUniv i
subst sub (j :< NeutMu x e) = do
  let sub' = filter (\(y, _) -> x /= y) sub
  let e' = subst sub' e
  j :< NeutMu x e'
subst sub (j :< NeutHole s) = fromMaybe (j :< NeutHole s) (lookup s sub)

substSigma :: Subst -> [(Identifier, Neut)] -> [(Identifier, Neut)]
substSigma _ [] = []
substSigma sub ((x, t):rest) = do
  let sub' = filter (\(y, _) -> y /= x) sub
  let xts = substSigma sub' rest
  let t' = subst sub t
  (x, t') : xts

reduceTerm :: Term -> WithEnv Term
reduceTerm app@(TermPiElim _ _) = do
  meta <- newNameWith "meta"
  let (fun, args) = toTermPiElimSeq app
  fun' <- reduceTerm fun
  case fun' of
    TermPiIntro x body ->
      reduceTerm $
      fromTermPiElimSeq (substTerm [(x, head args)] body, tail args)
    TermConst constant -> do
      args' <- mapM reduceTerm args
      let b1 = constant `elem` intAddConstantList
      let b2 = constant `elem` intSubConstantList
      let b3 = constant `elem` intMulConstantList
      let b4 = constant `elem` intDivConstantList
      case (b1, b2, b3, b4, takeIntegerList' args') of
        (True, _, _, _, Just [x, y]) ->
          return $ TermIndexIntro (IndexInteger (x + y)) meta
        (_, True, _, _, Just [x, y]) ->
          return $ TermIndexIntro (IndexInteger (x - y)) meta
        (_, _, True, _, Just [x, y]) ->
          return $ TermIndexIntro (IndexInteger (x * y)) meta
        (_, _, _, True, Just [x, y]) ->
          return $ TermIndexIntro (IndexInteger (x `div` y)) meta
        _ -> return $ fromTermPiElimSeq (fun', args')
    _ -> return $ fromTermPiElimSeq (fun', args)
reduceTerm (TermSigmaElim e xs body) = do
  e' <- reduceTerm e
  case e' of
    TermSigmaIntro es -> reduceTerm $ substTerm (zip xs es) body
    _ -> return $ TermSigmaElim e' xs body
reduceTerm (TermIndexElim e branchList) = do
  e' <- reduceTerm e
  case e' of
    TermIndexIntro x _ ->
      case lookup x branchList of
        Just body -> reduceTerm body
        Nothing ->
          case lookup IndexDefault branchList of
            Just body -> reduceTerm body
            Nothing ->
              lift $
              throwE $
              "the index " ++ show x ++ " is not included in branchList"
    _ -> return $ TermIndexElim e' branchList
reduceTerm (TermMu s e) = reduceTerm $ substTerm [(s, TermMu s e)] e
reduceTerm t = return t

type SubstTerm = [(Identifier, Term)]

substTerm :: SubstTerm -> Term -> Term
substTerm sub (TermVar s) = fromMaybe (TermVar s) (lookup s sub)
substTerm _ (TermConst x) = TermConst x
substTerm sub (TermPiIntro s body) = do
  let sub' = filter (\(x, _) -> x /= s) sub
  let body' = substTerm sub' body
  TermPiIntro s body'
substTerm sub (TermPiElim e1 e2) = do
  let e1' = substTerm sub e1
  let e2' = substTerm sub e2
  TermPiElim e1' e2'
substTerm sub (TermSigmaIntro es) = TermSigmaIntro (map (substTerm sub) es)
substTerm sub (TermSigmaElim e1 xs e2) = do
  let e1' = substTerm sub e1
  let sub' = filter (\(x, _) -> x `notElem` xs) sub
  let e2' = substTerm sub' e2
  TermSigmaElim e1' xs e2'
substTerm _ (TermIndexIntro l meta) = TermIndexIntro l meta
substTerm sub (TermIndexElim e branchList) = do
  let e' = substTerm sub e
  let branchList' = map (\(l, e) -> (l, substTerm sub e)) branchList
  TermIndexElim e' branchList'
substTerm sub (TermMu x e) = do
  let sub' = filter (\(y, _) -> x /= y) sub
  let e' = substTerm sub' e
  TermMu x e'

toPiIntroSeq :: Neut -> (Neut, [(Identifier, Neut, Identifier)])
toPiIntroSeq (meta :< NeutPiIntro (x, t) body) = do
  let (body', args) = toPiIntroSeq body
  (body', (x, t, meta) : args)
toPiIntroSeq t = (t, [])

toTermPiIntroSeq :: Term -> (Term, [Identifier])
toTermPiIntroSeq (TermPiIntro x body) = do
  let (body', args) = toTermPiIntroSeq body
  (body', x : args)
toTermPiIntroSeq t = (t, [])

toPiElimSeq :: Neut -> (Neut, [(Identifier, Neut)])
toPiElimSeq (i :< NeutPiElim e1 e2) = do
  let (fun, xs) = toPiElimSeq e1
  (fun, xs ++ [(i, e2)])
toPiElimSeq c = (c, [])

toTermPiElimSeq :: Term -> (Term, [Term])
toTermPiElimSeq (TermPiElim e1 e2) = do
  let (fun, xs) = toTermPiElimSeq e1
  (fun, xs ++ [e2])
toTermPiElimSeq c = (c, [])

fromPiElimSeq :: (Neut, [(Identifier, Neut)]) -> Neut
fromPiElimSeq (term, []) = term
fromPiElimSeq (term, (i, v):xs) = fromPiElimSeq (i :< NeutPiElim term v, xs)

fromTermPiElimSeq :: (Term, [Term]) -> Term
fromTermPiElimSeq (term, []) = term
fromTermPiElimSeq (term, v:xs) = fromTermPiElimSeq (TermPiElim term v, xs)

takeIntegerList :: [Neut] -> Maybe [Int]
takeIntegerList [] = Just []
takeIntegerList ((_ :< NeutIndexIntro (IndexInteger i)):rest) = do
  is <- takeIntegerList rest
  return (i : is)
takeIntegerList _ = Nothing

takeIntegerList' :: [Term] -> Maybe [Int]
takeIntegerList' [] = Just []
takeIntegerList' ((TermIndexIntro (IndexInteger i) _):rest) = do
  is <- takeIntegerList' rest
  return (i : is)
takeIntegerList' _ = Nothing

findDefault :: [(Index, Neut)] -> Maybe Neut
findDefault [] = Nothing
findDefault ((IndexDefault, e):_) = Just e
findDefault (_:rest) = findDefault rest

isReducible :: Neut -> Bool
isReducible (_ :< NeutVar _) = False
isReducible (_ :< NeutConst _) = False
isReducible (_ :< NeutPi (_, _) _) = False
isReducible (_ :< NeutPiIntro _ _) = False
isReducible (_ :< NeutPiElim (_ :< NeutPiIntro _ _) _) = True
isReducible (_ :< NeutPiElim e1 _) = isReducible e1
isReducible (_ :< NeutSigma _) = False
isReducible (_ :< NeutSigmaIntro es) = any isReducible es
isReducible (_ :< NeutSigmaElim (_ :< NeutSigmaIntro _) _ _) = True
isReducible (_ :< NeutSigmaElim e _ _) = isReducible e
isReducible (_ :< NeutIndex _) = False
isReducible (_ :< NeutIndexIntro _) = False
isReducible (_ :< NeutIndexElim (_ :< NeutIndexIntro _) _) = True
isReducible (_ :< NeutIndexElim e _) = isReducible e
isReducible (_ :< NeutUniv _) = False
isReducible (_ :< NeutMu _ _) = True
isReducible (_ :< NeutHole _) = False

reduceNeg :: Neg -> WithEnv Neg
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
reduceNeg (NegUpIntro e) = return $ NegUpIntro e
reduceNeg (NegUpElim x e1 e2) = do
  e1' <- reduceNeg e1
  e2' <- reduceNeg e2
  case e1' of
    NegUpIntro e1'' -> reduceNeg $ substNeg [(x, e1'')] e2'
    _ -> return $ NegUpElim x e1' e2'
reduceNeg (NegDownElim e) =
  case e of
    PosDownIntro e'' -> reduceNeg e''
    _ -> return $ NegDownElim e

-- reduceNeg (NegMu x e) = do
--   e' <- reduceNeg e
--   return $ NegMu x e'
type SubstPos = [(Identifier, Pos)]

substPos :: SubstPos -> Pos -> Pos
substPos sub (PosVar s) = fromMaybe (PosVar s) (lookup s sub)
substPos sub (PosSigmaIntro es) = do
  let es' = map (substPos sub) es
  PosSigmaIntro es'
substPos _ (PosIndexIntro l meta) = PosIndexIntro l meta
substPos sub (PosDownIntro e) = do
  let e' = substNeg sub e
  PosDownIntro e'

substNeg :: SubstPos -> Neg -> Neg
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
-- substNeg sub (NegMu x e) = NegMu x $ substNeg sub e
