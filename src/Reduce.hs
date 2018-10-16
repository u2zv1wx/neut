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
reducePos (Pos (meta :< PosDownIntro e)) = do
  e' <- reduceNeg e
  return $ Pos $ meta :< PosDownIntro e'
reducePos e = return e

reduceNeg :: Neg -> WithEnv Neg
reduceNeg (Neg (meta :< NegPiIntro x e)) = do
  Neg e' <- reduceNeg $ Neg e
  return $ Neg $ meta :< NegPiIntro x e'
reduceNeg (Neg (meta :< NegPiElim e1 e2)) = do
  Neg e1' <- reduceNeg $ Neg e1
  case e1' of
    _ :< NegPiIntro x body -> do
      let sub = [(x, e2)]
      let body' = substNeg sub $ Neg body
      reduceNeg body'
    _ -> return $ Neg $ meta :< NegPiElim e1' e2
reduceNeg (Neg (meta :< NegSigmaElim e xs body)) =
  case e of
    Pos (_ :< PosSigmaIntro es) -> do
      let sub = zip xs $ map Pos es
      let body' = substNeg sub $ Neg body
      reduceNeg body'
    _ -> do
      Neg body' <- reduceNeg $ Neg body
      return $ Neg $ meta :< NegSigmaElim e xs body'
reduceNeg (Neg (meta :< NegBoxElim e)) = do
  e' <- reducePos e
  case e' of
    Pos (_ :< PosBoxIntro e'') -> reduceNeg e''
    _ -> return $ Neg $ meta :< NegBoxElim e'
reduceNeg (Neg (meta :< NegIndexElim e branchList)) =
  case e of
    Pos (_ :< PosIndexIntro x) ->
      case lookup x branchList of
        Nothing ->
          lift $
          throwE $ "the index " ++ show x ++ " is not included in branchList"
        Just body -> reduceNeg $ Neg body
    _ -> return $ Neg $ meta :< NegIndexElim e branchList
reduceNeg (Neg (meta :< NegUpIntro e)) = do
  e' <- reducePos e
  return $ Neg $ meta :< NegUpIntro e'
reduceNeg (Neg (meta :< NegUpElim x e1 e2)) = do
  Neg e1' <- reduceNeg $ Neg e1
  Neg e2' <- reduceNeg $ Neg e2
  case e1' of
    _ :< NegUpIntro e1'' -> reduceNeg $ substNeg [(x, e1'')] $ Neg e2'
    _ -> return $ Neg $ meta :< NegUpElim x e1' e2'
reduceNeg (Neg (meta :< NegDownElim e)) = do
  e' <- reducePos e
  case e' of
    Pos (_ :< PosDownIntro e'') -> reduceNeg e''
    _ -> return $ Neg $ meta :< NegDownElim e'

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
substPos sub (Pos (meta :< PosVar s)) =
  fromMaybe (Pos $ meta :< PosVar s) (lookup s sub)
substPos _ (Pos (meta :< PosConst s)) = Pos $ meta :< PosConst s
substPos sub (Pos (meta :< PosSigma xts tcod)) = do
  let (xs, ts) = unzip xts
  let ts' = map (substPos sub . Pos) ts
  let ts'' = map (\(Pos x) -> x) ts'
  let Pos tcod' = substPos sub $ Pos tcod
  Pos $ meta :< PosSigma (zip xs ts'') tcod'
substPos sub (Pos (meta :< PosSigmaIntro es)) = do
  let es' = map (substPos sub . Pos) es
  let es'' = map (\(Pos x) -> x) es'
  Pos $ meta :< PosSigmaIntro es''
substPos sub (Pos (meta :< PosBox e)) = do
  let e' = substNeg sub e
  Pos $ meta :< PosBox e'
substPos sub (Pos (meta :< PosBoxIntro e)) = do
  let e' = substNeg sub e
  Pos $ meta :< PosBoxIntro e'
substPos _ (Pos (meta :< PosIndex x)) = Pos $ meta :< PosIndex x
substPos _ (Pos (meta :< PosIndexIntro l)) = Pos $ meta :< PosIndexIntro l
substPos _ (Pos (meta :< PosUniv)) = Pos $ meta :< PosUniv
substPos sub (Pos (meta :< PosDown e)) = do
  let e' = substNeg sub e
  Pos $ meta :< PosDown e'
substPos sub (Pos (meta :< PosDownIntro e)) = do
  let e' = substNeg sub e
  Pos $ meta :< PosDownIntro e'

substNeg :: SubstPos -> Neg -> Neg
substNeg sub (Neg (meta :< NegPi (s, tdom) tcod)) = do
  let tdom' = substPos sub tdom
  let Neg tcod' = substNeg sub $ Neg tcod
  Neg $ meta :< NegPi (s, tdom') tcod'
substNeg sub (Neg (meta :< NegPiIntro s body)) = do
  let Neg body' = substNeg sub $ Neg body
  Neg $ meta :< NegPiIntro s body'
substNeg sub (Neg (meta :< NegPiElim e1 e2)) = do
  let Neg e1' = substNeg sub $ Neg e1
  let e2' = substPos sub e2
  Neg $ meta :< NegPiElim e1' e2'
substNeg sub (Neg (meta :< NegSigmaElim e1 xs e2)) = do
  let e1' = substPos sub e1
  let Neg e2' = substNeg sub $ Neg e2
  Neg $ meta :< NegSigmaElim e1' xs e2'
substNeg sub (Neg (meta :< NegBoxElim e)) = do
  let e' = substPos sub e
  Neg $ meta :< NegBoxElim e'
substNeg sub (Neg (meta :< NegIndexElim e branchList)) = do
  let e' = substPos sub e
  let branchList' = map (\(l, e) -> (l, substNeg sub $ Neg e)) branchList
  let branchList'' = map (\(l, Neg e) -> (l, e)) branchList'
  Neg $ meta :< NegIndexElim e' branchList''
substNeg sub (Neg (meta :< NegUpIntro e)) =
  Neg $ meta :< NegUpIntro (substPos sub e)
substNeg sub (Neg (meta :< NegUpElim x e1 e2)) = do
  let Neg e1' = substNeg sub $ Neg e1
  let Neg e2' = substNeg sub $ Neg e2
  Neg $ meta :< NegUpElim x e1' e2'
substNeg sub (Neg (meta :< NegDownElim e)) =
  Neg $ meta :< NegDownElim (substPos sub e)

findInvVar :: Subst -> Identifier -> Maybe Identifier
findInvVar [] _ = Nothing
findInvVar ((y, _ :< NeutVar x):rest) x'
  | x == x' =
    if not (any (/= y) $ findInvVar' rest x')
      then Just y
      else Nothing
findInvVar ((_, _):rest) i = findInvVar rest i

findInvVar' :: Subst -> Identifier -> [Identifier]
findInvVar' [] _ = []
findInvVar' ((z, _ :< NeutVar x):rest) x'
  | x /= x' = z : findInvVar' rest x'
findInvVar' (_:rest) x' = findInvVar' rest x'

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
