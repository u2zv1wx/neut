module Pattern
  ( toDecision
  , patDist
  , swap
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
toDecision _ ([], _) = return $ DecisionFail
toDecision _ (_, []) = return $ DecisionFail
toDecision os (patMat, bodyList)
  | Nothing <- findPatApp patMat = do
    liftIO $ putStrLn $ "found Leaf. the patMat is:\n" ++ Pr.ppShow patMat
    liftIO $ putStrLn $ "and the occurrence vector is:\n" ++ Pr.ppShow os
    let vs = collectVar patMat
    return $ DecisionLeaf vs (head bodyList)
  | Just i <- findPatApp patMat
  , i /= 0 = do
    let patMat' = swapColumn 0 i patMat
    let os' = swapColumn 0 i os
    DecisionSwap i <$> toDecision os' (patMat', bodyList)
  | otherwise = do
    consList <- nub <$> headConstructor patMat
    newMatrixList <-
      forM consList $ \(c, a) -> do
        let os' = (map (\j -> head os ++ [j]) [1 .. a]) ++ tail os
        (tmp, _) <- specialize c a (patMat, bodyList)
        tmp' <- toDecision os' tmp
        return ((c, []), tmp')
    cenv <- getCEnv patMat
    if length cenv <= length consList
      then return $ DecisionSwitch (head os) $ newMatrixList
      else do
        (tmp, bounds) <- defaultMatrix (patMat, bodyList)
        dmat <- toDecision (tail os) $ tmp
        return $
          DecisionSwitch (head os) $
          newMatrixList ++ [(("default", bounds), dmat)]

patDist :: [([Pat], a)] -> ([[Pat]], [a])
patDist [] = ([], [])
patDist ((ps, body):rest) = do
  let (pss, bodyList) = patDist rest
  (ps : pss, body : bodyList)

type Arity = Int

getCEnv :: [[Pat]] -> WithEnv [Identifier]
getCEnv [] = lift $ throwE "empty pattern"
getCEnv ([]:_) = lift $ throwE "empty pattern"
getCEnv (((Meta {ident = i} :< _):_):_) = do
  t <- lookupWTEnv i
  case t of
    Just (WeakTypeNode s _) -> lookupConstructorEnv s
    _                       -> undefined

headConstructor :: [[Pat]] -> WithEnv [(Identifier, Arity)]
headConstructor ([]) = return []
headConstructor (ps:pss) = do
  ps' <- headConstructor' ps
  pss' <- mapM headConstructor' pss
  return $ join $ ps' : pss'

headConstructor' :: [Pat] -> WithEnv [(Identifier, Arity)]
headConstructor' []                       = return []
headConstructor' ((_ :< PatVar _):_)      = return []
headConstructor' ((_ :< PatApp s args):_) = return [(s, length args)]

collectVar :: [[Pat]] -> [Identifier]
collectVar [] = []
collectVar (ps:pss) = do
  let vs1 = collectVar' ps
  let vs2 = collectVar pss
  vs1 ++ vs2

collectVar' :: [Pat] -> [Identifier]
collectVar' []                   = []
collectVar' ((_ :< PatVar s):ps) = s : collectVar' ps
collectVar' (_:ps)               = collectVar' ps

findPatApp :: [[Pat]] -> Maybe Int
findPatApp [] = Nothing
findPatApp (ps:pss) =
  case findPatApp' $ zip ps [0 ..] of
    Nothing -> findPatApp pss
    Just i  -> Just i

findPatApp' :: [(Pat, Int)] -> Maybe Int
findPatApp' []                       = Nothing
findPatApp' ((_ :< PatVar _, _):ps)  = findPatApp' ps
findPatApp' ((_ :< PatApp _ _, i):_) = Just i

specialize ::
     Identifier
  -> Arity
  -> ClauseMatrix a
  -> WithEnv ((ClauseMatrix a), [Identifier])
specialize c a (pss, bs) = do
  pss' <- mapM (\(ps, b) -> specializeRow c a ps b) $ zip pss bs
  let pss'' = map fst pss'
  let bounds = join $ map snd pss'
  return (patDist $ join pss'', bounds)

specializeRow ::
     Identifier -> Arity -> [Pat] -> a -> WithEnv ([([Pat], a)], [Identifier])
specializeRow _ _ [] _ = return ([], [])
specializeRow _ a ((i :< PatVar s):ps) body = do
  liftIO $ putStrLn $ "BINDING: " ++ show s
  newNames <-
    forM [1 .. a] $ \_ -> do
      k <- newName
      return $ i :< PatVar k
  return ([(newNames ++ ps, body)], [s])
specializeRow c _ ((_ :< PatApp s args):ps) body = do
  if c /= s
    then return ([], [])
    else return ([(args ++ ps, body)], [])

defaultMatrix :: ClauseMatrix a -> WithEnv ((ClauseMatrix a), [Identifier])
defaultMatrix (pss, bs) = do
  pss' <- mapM (\(ps, b) -> defaultMatrixRow ps b) $ zip pss bs
  let pss'' = map fst pss'
  let bounds = join $ map snd pss'
  return (patDist $ join pss'', bounds)

defaultMatrixRow :: [Pat] -> a -> WithEnv ([([Pat], a)], [Identifier])
defaultMatrixRow [] _ = return ([], [])
defaultMatrixRow ((_ :< PatVar s):ps) body = do
  return ([(ps, body)], [s])
defaultMatrixRow ((_ :< PatApp _ _):_) _ = return ([], [])

swapColumn :: Int -> Int -> [[a]] -> [[a]]
swapColumn i j mat = transpose $ swap i j $ transpose mat

swap :: Int -> Int -> [a] -> [a]
swap i j xs = do
  replaceNth j (xs !! i) (replaceNth i (xs !! j) xs)

replaceNth :: Int -> a -> [a] -> [a]
replaceNth _ _ [] = []
replaceNth n newVal (x:xs)
  | n == 0 = newVal : xs
  | otherwise = x : replaceNth (n - 1) newVal xs
