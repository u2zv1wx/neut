module Pattern
  ( toDecision
  , patDist
  ) where

import           Control.Comonad.Cofree

import           Control.Monad
import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Data
import           Data.List                  (nub, transpose)

import           Debug.Trace

import qualified Text.Show.Pretty           as Pr

type ClauseMatrix a = ([[Pat]], [a])

-- Muranget, "Compiling Pattern Matching to Good Decision Trees", 2008
toDecision :: (Show a) => [Occurrence] -> ClauseMatrix a -> WithEnv (Decision a)
toDecision _ ([], _) = lift $ throwE "non-exclusive pattern"
toDecision _ (_, []) = lift $ throwE "non-exclusive pattern"
toDecision os (patMat, bodyList)
  | Nothing <- findPatApp patMat = do
    vs <- collectVar patMat
    return $ DecisionLeaf (zip os vs) (head bodyList)
  | Just i <- findPatApp patMat
  , i /= 0 = do
    let patMat' = swapColumn 0 i patMat
    let os' = swapColumn 0 i os
    DecisionSwap i <$> toDecision os' (patMat', bodyList)
  | otherwise = do
    consList <- nub <$> headConstructor patMat
    newMatrixList <-
      forM consList $ \(c, num, a) -> do
        let os' = map (\j -> head os ++ [j]) [0 .. (a - 1)] ++ tail os
        tmp <- specialize c a (patMat, bodyList)
        tmp' <- toDecision os' tmp
        return ((c, num), tmp')
    cenv <- getCEnv patMat
    if length cenv <= length consList
      then return $ DecisionSwitch (head os) newMatrixList Nothing
      else do
        (tmp, bounds) <- defaultMatrix (patMat, bodyList)
        dmat <- toDecision (tail os) tmp
        return $ DecisionSwitch (head os) newMatrixList (Just (bounds, dmat))

patDist :: [([Pat], a)] -> ([[Pat]], [a])
patDist [] = ([], [])
patDist ((ps, body):rest) = do
  let (pss, bodyList) = patDist rest
  (ps : pss, body : bodyList)

type Arity = Int

getCEnv :: [[Pat]] -> WithEnv [Identifier]
getCEnv [] = lift $ throwE "empty pattern"
getCEnv ([]:_) = lift $ throwE "empty pattern"
getCEnv (((i :< _):_):_) = do
  t <- lookupTypeEnv i
  case t of
    Just (Fix (TypeNode s _)) -> lookupConstructorEnv s
    _                         -> lift $ throwE "type error in pattern"

headConstructor :: [[Pat]] -> WithEnv [(Identifier, Int, Int)]
headConstructor [] = return []
headConstructor (ps:pss) = do
  ps' <- headConstructor' ps
  pss' <- mapM headConstructor' pss
  return $ join $ ps' : pss'

headConstructor' :: [Pat] -> WithEnv [(Identifier, Int, Int)]
headConstructor' [] = return []
headConstructor' ((_ :< PatHole):_) = return []
headConstructor' ((_ :< PatVar _):_) = return []
headConstructor' ((i :< PatApp s _):_) = do
  t <- lookupTypeEnv i
  case t of
    Just (Fix (TypeNode node _)) -> do
      (_, args, _) <- lookupVEnv' s
      i <- getConstructorNumber node s
      return [(s, i, length args)]
    _ -> lift $ throwE $ s ++ " is not a constructor"

collectVar :: [[Pat]] -> WithEnv [Identifier]
collectVar [] = return []
collectVar (ps:pss) = do
  vs1 <- collectVar' ps
  vs2 <- collectVar pss
  return $ vs1 ++ vs2

collectVar' :: [Pat] -> WithEnv [Identifier]
collectVar' [] = return []
collectVar' ((_ :< PatVar s):ps) = do
  tmp <- collectVar' ps
  return $ s : tmp
collectVar' (_:ps) = collectVar' ps

findPatApp :: [[Pat]] -> Maybe Int
findPatApp [] = Nothing
findPatApp (ps:pss) =
  case findPatApp' $ zip ps [0 ..] of
    Nothing -> findPatApp pss
    Just i  -> Just i

findPatApp' :: [(Pat, Int)] -> Maybe Int
findPatApp' []                       = Nothing
findPatApp' ((_ :< PatHole, _):ps)   = findPatApp' ps
findPatApp' ((_ :< PatVar _, _):ps)  = findPatApp' ps
findPatApp' ((_ :< PatApp _ _, i):_) = Just i

specialize :: Identifier -> Arity -> ClauseMatrix a -> WithEnv (ClauseMatrix a)
specialize c a (pss, bs) = do
  pss' <- zipWithM (specializeRow c a) pss bs
  return $ patDist $ join pss'

specializeRow :: Identifier -> Arity -> [Pat] -> a -> WithEnv [([Pat], a)]
specializeRow _ _ [] _ = return []
specializeRow _ a ((i :< PatHole):ps) body = do
  newNames <- forM [1 .. a] $ const $ return $ i :< PatHole
  return [(newNames ++ ps, body)]
specializeRow c a ((i :< PatVar _):ps) body =
  specializeRow c a ((i :< PatHole) : ps) body
specializeRow c _ ((_ :< PatApp s args):ps) body =
  if c /= s
    then return []
    else return [(args ++ ps, body)]

defaultMatrix :: ClauseMatrix a -> WithEnv (ClauseMatrix a, Maybe Identifier)
defaultMatrix (pss, bs) = do
  pss' <- zipWithM defaultMatrixRow pss bs
  let pss'' = map fst pss'
  let bounds = takeHeadJust $ map snd pss'
  return (patDist $ join pss'', bounds)

takeHeadJust :: [Maybe a] -> Maybe a
takeHeadJust []             = Nothing
takeHeadJust (Nothing:rest) = takeHeadJust rest
takeHeadJust (Just x:_)     = Just x

defaultMatrixRow :: [Pat] -> a -> WithEnv ([([Pat], a)], Maybe Identifier)
defaultMatrixRow [] _                      = return ([], Nothing)
defaultMatrixRow ((_ :< PatHole):ps) body  = return ([(ps, body)], Nothing)
defaultMatrixRow ((_ :< PatVar s):ps) body = return ([(ps, body)], Just s)
defaultMatrixRow ((_ :< PatApp _ _):_) _   = return ([], Nothing)

swapColumn :: Int -> Int -> [[a]] -> [[a]]
swapColumn i j mat = transpose $ swap i j $ transpose mat
