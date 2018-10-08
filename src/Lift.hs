module Lift
  ( lift
  ) where

import           Control.Comonad.Cofree
import           Control.Monad
import           Control.Monad.State        hiding (lift)
import           Control.Monad.Trans.Except

import qualified Text.Show.Pretty           as Pr

import           Data
import           Reduce
import           Util

lift :: Neut -> WithEnv Neut
lift v@(_ :< NeutVar _) = return v
lift v@(_ :< NeutConst _ _) = return v
lift (i :< NeutPi (x, tdom) tcod) = do
  tdom' <- lift tdom
  tcod' <- lift tcod
  return $ i :< NeutPi (x, tdom') tcod'
lift lam@(i :< NeutPiIntro _ _) = do
  let (body, xtms) = toPiIntroSeq lam
  body' <- lift body
  let xs = map (\(x, _, _) -> x) xtms
  let freeVars = filter (`notElem` xs) $ var body'
  newFormalArgs <- constructFormalArgs freeVars
  let freeToBound = zip freeVars newFormalArgs
  body'' <- replace freeToBound body'
  lamType <- lookupTypeEnv' i
  ytms <- enrich lamType newFormalArgs
  let lam' = fromPiIntroSeq (body'', ytms ++ xtms)
  args <- mapM toVar freeVars
  appFold lam' args
lift (i :< NeutPiElim e v) = do
  e' <- lift e
  v' <- lift v
  return $ i :< NeutPiElim e' v'
lift (i :< NeutSigma xts tcod) = do
  let (xs, ts) = unzip xts
  ts' <- mapM lift ts
  tcod' <- lift tcod
  return $ i :< NeutSigma (zip xs ts') tcod'
lift (i :< NeutSigmaIntro es) = do
  es' <- mapM lift es
  return $ i :< NeutSigmaIntro es'
lift (i :< NeutSigmaElim e1 xs e2) = do
  e1' <- lift e1
  e2' <- lift e2
  return $ i :< NeutSigmaElim e1' xs e2'
lift (i :< NeutBox e) = do
  e' <- lift e
  return $ i :< NeutBox e'
lift (i :< NeutBoxIntro e) = do
  e' <- lift e
  return $ i :< NeutBoxIntro e'
lift (i :< NeutBoxElim e) = do
  e' <- lift e
  return $ i :< NeutBoxElim e'
lift (i :< NeutIndex l) = return $ i :< NeutIndex l
lift (i :< NeutIndexIntro x) = return $ i :< NeutIndexIntro x
lift (i :< NeutIndexElim e branchList) = do
  e' <- lift e
  let (indexList, es) = unzip branchList
  es' <- mapM lift es
  return $ i :< NeutIndexElim e' (zip indexList es')
lift (i :< NeutUniv j) = return $ i :< NeutUniv j
lift (i :< NeutMu s c) = do
  c' <- lift c
  return $ i :< NeutMu s c'
lift (i :< NeutHole x) = return $ i :< NeutHole x

replace :: [(Identifier, Identifier)] -> Neut -> WithEnv Neut
replace f2b (i :< NeutVar s) =
  case lookup s f2b of
    Nothing -> return $ i :< NeutVar s
    Just b -> do
      t <- lookupTypeEnv' i
      insTypeEnv b t
      return $ i :< NeutVar b
replace _ (i :< NeutConst x t) = return $ i :< NeutConst x t
replace args (i :< NeutPi (x, tdom) tcod) = do
  tdom' <- replace args tdom
  tcod' <- replace args tcod
  return $ i :< NeutPi (x, tdom') tcod'
replace args (i :< NeutPiIntro x e) = do
  e' <- replace args e
  return $ i :< NeutPiIntro x e'
replace args (i :< NeutPiElim e v) = do
  e' <- replace args e
  v' <- replace args v
  return $ i :< NeutPiElim e' v'
replace args (i :< NeutSigma xts tcod) = do
  let (xs, ts) = unzip xts
  ts' <- mapM (replace args) ts
  -- tdom' <- replace args tdom
  tcod' <- replace args tcod
  return $ i :< NeutSigma (zip xs ts') tcod'
replace args (i :< NeutSigmaIntro es) = do
  es' <- mapM (replace args) es
  return $ i :< NeutSigmaIntro es'
replace args (i :< NeutSigmaElim e1 xs e2) = do
  e1' <- replace args e1
  e2' <- replace args e2
  return $ i :< NeutSigmaElim e1' xs e2'
replace args (i :< NeutBox e) = do
  e' <- replace args e
  return $ i :< NeutBox e'
replace args (i :< NeutBoxIntro e) = do
  e' <- replace args e
  return $ i :< NeutBoxIntro e'
replace args (i :< NeutBoxElim e) = do
  e' <- replace args e
  return $ i :< NeutBoxElim e'
replace _ (i :< NeutIndex l) = return $ i :< NeutIndex l
replace _ (i :< NeutIndexIntro x) = return $ i :< NeutIndexIntro x
replace args (i :< NeutIndexElim e branchList) = do
  e' <- replace args e
  let (indexList, es) = unzip branchList
  es' <- mapM (replace args) es
  return $ i :< NeutIndexElim e' (zip indexList es')
replace _ (i :< NeutUniv j) = return $ i :< NeutUniv j
replace args (i :< NeutMu s c) = do
  c' <- replace args c
  return $ i :< NeutMu s c'
replace _ (i :< NeutHole x) = return $ i :< NeutHole x

enrich :: Neut -> [Identifier] -> WithEnv [(Identifier, Neut, Identifier)]
enrich _ [] = return []
enrich cod (x:xs) = do
  pi <- abstractPi (x : xs) cod
  meta <- newNameWith "meta"
  insTypeEnv meta pi
  xtms <- enrich cod xs
  return $ (x, pi, meta) : xtms
