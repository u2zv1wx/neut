module Resource where

import           Control.Monad

import           Control.Comonad.Cofree

import           Control.Monad.State
import           Control.Monad.Trans.Except

import qualified Text.Show.Pretty           as Pr

import           Data
import           Data.Maybe                 (maybeToList)

insCopyFree :: Neut -> WithEnv Neut
insCopyFree e = insCopy [] e >>= \(e', _) -> insFree e'

insCopy :: [Identifier] -> Neut -> WithEnv (Neut, [Identifier])
insCopy found v@(i :< NeutVar x) =
  if x `notElem` found
    then return (v, [x]) -- the final occurrence of x
    else do
      tmp <- newNameWith "copy"
      meta <- newNameWith "meta"
      -- Copy the content of a variable if it's not the final occurrence.
      let e = meta :< NeutCopy tmp x (i :< NeutVar tmp)
      return (e, [])
insCopy found (i :< NeutPi (x, tdom) tcod) = do
  (tdom', vs1) <- insCopy found tdom
  (tcod', vs2) <- insCopy found tcod
  return (i :< NeutPi (x, tdom') tcod', found ++ vs1 ++ vs2)
insCopy found (i :< NeutPiIntro arg body) = do
  (body', vs) <- insCopy found body
  return (i :< NeutPiIntro arg body', found ++ vs)
insCopy found (i :< NeutPiElim e1 e2) = do
  (e1', vs1) <- insCopy found e1
  -- Note that this function is order-sensitive.
  -- Here, for example, e1 needs to be evaluated earlier than e2 to
  -- determine the "final" occurrence of a variable.
  (e2', vs2) <- insCopy (vs1 ++ found) e2
  return (i :< NeutPiElim e1' e2', found ++ vs1 ++ vs2)
insCopy found (i :< NeutSigma (x, tdom) tcod) = do
  (tcod', vs2) <- insCopy found tcod
  (tdom', vs1) <- insCopy found tdom
  return (i :< NeutSigma (x, tdom') tcod', found ++ vs1 ++ vs2)
insCopy found (i :< NeutSigmaIntro v1 v2) = do
  (v2', vs2) <- insCopy found v2
  (v1', vs1) <- insCopy (vs2 ++ found) v1
  return (i :< NeutSigmaIntro v1' v2', found ++ vs1 ++ vs2)
insCopy found (i :< NeutSigmaElim e1 (x, y) e2) = do
  (e2', vs2) <- insCopy found e2
  (e1', vs1) <- insCopy (vs2 ++ found) e1
  return (i :< NeutSigmaElim e1' (x, y) e2', found ++ vs1 ++ vs2)
insCopy _ (i :< NeutIndex l) = return (i :< NeutIndex l, [])
insCopy _ (i :< NeutIndexIntro x) = return (i :< NeutIndexIntro x, [])
insCopy found (i :< NeutIndexElim e branchList) = do
  let (indexList, es) = unzip branchList
  evs' <- mapM (insCopy found) es
  let (es', vss) = unzip evs'
  let vs = join vss
  (e', vs') <- insCopy (vs ++ found) e
  return (i :< NeutIndexElim e' (zip indexList es'), found ++ vs ++ vs')
insCopy _ (i :< NeutUniv j) = return (i :< NeutUniv j, [])
insCopy found (i :< NeutCopy tmp x e) = do
  (e', vs) <- insCopy found e
  return (i :< NeutCopy tmp x e', found ++ vs)
insCopy found (i :< NeutFree x e) = do
  (e', vs) <- insCopy found e
  return (i :< NeutFree x e', found ++ vs)
insCopy _ (i :< NeutHole x) = return (i :< NeutHole x, [])
insCopy found (meta :< NeutMu s c) = do
  (c', vs) <- insCopy found c
  return (meta :< NeutMu s c', found ++ vs)

-- free all the unused variables before evaluating the body of a lambda abstraction
insFree :: Neut -> WithEnv Neut
insFree (i :< NeutVar x) = return $ i :< NeutVar x
insFree (i :< NeutPi (x, tdom) tcod) = do
  tdom' <- insFree tdom
  tcod' <- insFree tcod
  return $ i :< NeutPi (x, tdom') tcod'
insFree lam@(_ :< NeutPiIntro _ _) = do
  (body, argTypeMetaList) <- toPiIntroSeq lam
  -- let args = map (\(x, _, _) -> x) argTypeMetaList
  vs <- var body
  let unusedVarList = filter (\(x, _, _) -> x `notElem` vs) argTypeMetaList
  body' <- insFree' (map (\(x, _, _) -> x) unusedVarList) body
  return $ fromPiIntroSeq (body', argTypeMetaList)
insFree (i :< NeutPiElim e1 e2) = do
  e1' <- insFree e1
  e2' <- insFree e2
  return $ i :< NeutPiElim e1' e2'
insFree (i :< NeutSigma (x, tdom) tcod) = do
  tdom' <- insFree tdom
  tcod' <- insFree tcod
  return $ i :< NeutSigma (x, tdom') tcod'
insFree (i :< NeutSigmaIntro v1 v2) = do
  v1' <- insFree v1
  v2' <- insFree v2
  return $ i :< NeutSigmaIntro v1' v2'
insFree (i :< NeutSigmaElim e1 (x, y) e2) = do
  e1' <- insFree e1
  e2' <- insFree e2
  vs <- var e2'
  let unusedVarList = filter (`notElem` vs) [x, y]
  e2'' <- insFree' unusedVarList e2'
  return $ i :< NeutSigmaElim e1' (x, y) e2''
insFree (i :< NeutIndex l) = return $ i :< NeutIndex l
insFree (i :< NeutIndexIntro x) = return $ i :< NeutIndexIntro x
insFree (i :< NeutIndexElim e branchList) = do
  e' <- insFree e
  let (indexList, es) = unzip branchList
  es' <- mapM insFree es
  return $ i :< NeutIndexElim e' (zip indexList es')
insFree (i :< NeutUniv j) = return $ i :< NeutUniv j
insFree (meta :< NeutMu s c) = do
  c' <- insFree c
  return $ meta :< NeutMu s c'
insFree (i :< NeutCopy tmp x e) = do
  e' <- insFree e
  vs <- var e
  let unusedVarList = filter (`notElem` vs) [tmp]
  e'' <- insFree' unusedVarList e'
  return $ i :< NeutCopy tmp x e''
insFree (i :< NeutFree x e) = do
  e' <- insFree e
  return $ i :< NeutFree x e'
insFree (i :< NeutHole x) = return $ i :< NeutHole x

insFree' :: [Identifier] -> Neut -> WithEnv Neut
insFree' [] e = return e
insFree' (x:xs) e = do
  meta <- newNameWith "meta"
  e' <- insFree' xs e
  return $ meta :< NeutFree x e'
