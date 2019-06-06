module Reduce where

import           Data

import           Control.Comonad

import           Control.Comonad.Cofree
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Text.Show.Deriving

import           Data.Functor.Classes

import           System.IO.Unsafe

import           Data.IORef
import           Data.List
import           Data.Maybe                 (fromMaybe)
import           Data.Tuple                 (swap)

import qualified Text.Show.Pretty           as Pr

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
      let t = LowTypeSignedInt 64 -- for now
      case (b1, b2, b3, b4, takeIntegerList' args') of
        (True, _, _, _, Just [x, y]) ->
          return $ TermIndexIntro (IndexInteger (x + y)) t
        (_, True, _, _, Just [x, y]) ->
          return $ TermIndexIntro (IndexInteger (x - y)) t
        (_, _, True, _, Just [x, y]) ->
          return $ TermIndexIntro (IndexInteger (x * y)) t
        (_, _, _, True, Just [x, y]) ->
          return $ TermIndexIntro (IndexInteger (x `div` y)) t
        _ -> return $ fromTermPiElimSeq (fun', args')
    _ -> return $ fromTermPiElimSeq (fun', args)
reduceTerm (TermSigmaElim e xs body) = do
  e' <- reduceTerm e
  case e' of
    TermSigmaIntro es -> reduceTerm $ substTerm (zip xs es) body
    _                 -> return $ TermSigmaElim e' xs body
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

substTerm' :: SubstTerm -> Term -> Term
substTerm' _ (TermVar x) = TermVar x
substTerm' sub (TermConst x) = fromMaybe (TermConst x) (lookup x sub)
substTerm' sub (TermPiIntro s body) = do
  let sub' = filter (\(x, _) -> x /= s) sub
  let body' = substTerm' sub' body
  TermPiIntro s body'
substTerm' sub (TermPiElim e1 e2) = do
  let e1' = substTerm' sub e1
  let e2' = substTerm' sub e2
  TermPiElim e1' e2'
substTerm' sub (TermSigmaIntro es) = TermSigmaIntro (map (substTerm' sub) es)
substTerm' sub (TermSigmaElim e1 xs e2) = do
  let e1' = substTerm' sub e1
  let sub' = filter (\(x, _) -> x `notElem` xs) sub
  let e2' = substTerm' sub' e2
  TermSigmaElim e1' xs e2'
substTerm' _ (TermIndexIntro l meta) = TermIndexIntro l meta
substTerm' sub (TermIndexElim e branchList) = do
  let e' = substTerm' sub e
  let branchList' = map (\(l, e) -> (l, substTerm' sub e)) branchList
  TermIndexElim e' branchList'

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
fromPiElimSeq (term, [])        = term
fromPiElimSeq (term, (i, v):xs) = fromPiElimSeq (i :< NeutPiElim term v, xs)

fromTermPiElimSeq :: (Term, [Term]) -> Term
fromTermPiElimSeq (term, [])   = term
fromTermPiElimSeq (term, v:xs) = fromTermPiElimSeq (TermPiElim term v, xs)

takeIntegerList :: [Neut] -> Maybe [Int]
takeIntegerList [] = Just []
takeIntegerList ((_ :< NeutIndexIntro (IndexInteger i)):rest) = do
  is <- takeIntegerList rest
  return (i : is)
takeIntegerList _ = Nothing

takeIntegerList' :: [Term] -> Maybe [Int]
takeIntegerList' [] = Just []
takeIntegerList' (TermIndexIntro (IndexInteger i) _:rest) = do
  is <- takeIntegerList' rest
  return (i : is)
takeIntegerList' _ = Nothing

takeIntegerList'' :: [Pos] -> Maybe [Int]
takeIntegerList'' [] = Just []
takeIntegerList'' (PosIndexIntro (IndexInteger i) _:rest) = do
  is <- takeIntegerList'' rest
  return (i : is)
takeIntegerList'' _ = Nothing

findDefault :: [(Index, Neut)] -> Maybe Neut
findDefault []                    = Nothing
findDefault ((IndexDefault, e):_) = Just e
findDefault (_:rest)              = findDefault rest

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
reduceNeg (NegPiElimDownElim v1 v2) =
  case v1 of
    PosConst x -> do
      penv <- gets polEnv
      case lookup x penv of
        Just (DeclarationFun arg body) -> reduceNeg $ substNeg [(arg, v2)] body
        Just (DeclarationConst v1') -> reduceNeg $ NegPiElimDownElim v1' v2
        _ -> return $ NegPiElimDownElim v1 v2
    _ -> return $ NegPiElimDownElim v1 v2
reduceNeg (NegSigmaElim v xs body) =
  case v of
    PosSigmaIntro vs
      | length xs == length vs -> reduceNeg $ substNeg (zip xs vs) body
    PosConst x -> do
      penv <- gets polEnv
      case lookup x penv of
        Just (DeclarationConst v') -> reduceNeg $ NegSigmaElim v' xs body
        _ -> do
          liftIO $ putStrLn $ "not found: " ++ show x
          return $ NegSigmaElim v xs body
    _ -> return $ NegSigmaElim v xs body
reduceNeg (NegIndexElim v branchList) =
  case v of
    PosIndexIntro x _ ->
      case lookup x branchList of
        Just body -> reduceNeg body
        Nothing ->
          case lookup IndexDefault branchList of
            Just body -> reduceNeg body
            Nothing ->
              lift $
              throwE $
              "the index " ++ show x ++ " is not included in branchList"
    _ -> return $ NegIndexElim v branchList
reduceNeg (NegUpElim x e1 e2) = do
  e1' <- reduceNeg e1
  case e1' of
    NegUpIntro v -> reduceNeg $ substNeg [(x, v)] e2
    _            -> return $ NegUpElim x e1' e2
reduceNeg (NegConstElim x vs) = do
  let xs = takeIntegerList'' vs
  let t = LowTypeSignedInt 64 -- for now
  case (x, xs) of
    (ConstantArith _ ArithAdd, Just [x, y]) ->
      return $ NegUpIntro (PosIndexIntro (IndexInteger (x + y)) t)
    (ConstantArith _ ArithSub, Just [x, y]) ->
      return $ NegUpIntro (PosIndexIntro (IndexInteger (x - y)) t)
    (ConstantArith _ ArithMul, Just [x, y]) ->
      return $ NegUpIntro (PosIndexIntro (IndexInteger (x * y)) t)
    (ConstantArith _ ArithDiv, Just [x, y]) ->
      return $ NegUpIntro (PosIndexIntro (IndexInteger (x `div` y)) t)
    _ -> return $ NegConstElim x vs
reduceNeg e = return e

type SubstPos = [(Identifier, Pos)]

substPos :: SubstPos -> Pos -> Pos
substPos sub (PosVar s) = fromMaybe (PosVar s) (lookup s sub)
substPos _ (PosConst s) = PosConst s
substPos sub (PosSigmaIntro vs) = do
  let vs' = map (substPos sub) vs
  PosSigmaIntro vs'
substPos _ (PosIndexIntro l t) = PosIndexIntro l t

substNeg :: SubstPos -> Neg -> Neg
substNeg sub (NegPiElimDownElim v1 v2) = do
  let v1' = substPos sub v1
  let v2' = substPos sub v2
  NegPiElimDownElim v1' v2'
substNeg sub (NegSigmaElim v xs e) = do
  let v' = substPos sub v
  let sub' = filter (\(x, _) -> x `notElem` xs) sub
  let e' = substNeg sub' e
  NegSigmaElim v' xs e'
substNeg sub (NegIndexElim v branchList) = do
  let v' = substPos sub v
  let branchList' = map (\(l, e) -> (l, substNeg sub e)) branchList
  NegIndexElim v' branchList'
substNeg sub (NegUpIntro v) = NegUpIntro $ substPos sub v
substNeg sub (NegUpElim x e1 e2) = do
  let e1' = substNeg sub e1
  let sub' = filter (\(y, _) -> x /= y) sub
  let e2' = substNeg sub' e2
  NegUpElim x e1' e2'
substNeg sub (NegConstElim x vs) = NegConstElim x $ map (substPos sub) vs
